{-
(c) The GRASP/AQUA Project, Glasgow University, 1992-2012


Note [Unarisation]
~~~~~~~~~~~~~~~~~~
The idea of this pass is to translate away *all* unboxed-tuple binders.
So for example:

f (x :: (# Int, Bool #)) = f x + f (# 1, True #)
 ==>
f (x1 :: Int) (x2 :: Bool) = f x1 x2 + f 1 True

It is important that we do this at the STG level and NOT at the core level
because it would be very hard to make this pass Core-type-preserving. In
this example the type of 'f' changes, for example.

STG fed to the code generators *must* be unarised because the code generators do
not support unboxed tuple binders natively.

In more detail:

Suppose that a variable x : (# t1, t2 #).

  * At the binding site for x, make up fresh vars  x1:t1, x2:t2

  * Extend the UnariseEnv   x :-> [x1,x2]

  * Replace the binding with a curried binding for x1,x2
       Lambda:   \x.e                ==>   \x1 x2. e
       Case alt: MkT a b x c d -> e  ==>   MkT a b x1 x2 c d -> e

  * Replace argument occurrences with a sequence of args
    via a lookup in UnariseEnv
       f a b x c d   ==>   f a b x1 x2 c d

  * Replace tail-call occurrences with an unboxed tuple
    via a lookup in UnariseEnv
       x  ==>  (# x1, x2 #)
    So, for example
       f x = x    ==>   f x1 x2 = (# x1, x2 #)

    This applies to case scrutinees too
       case x of (# a,b #) -> e   ==>   case (# x1,x2 #) of (# a,b #) -> e
    I think we rely on the code generator to short-circuit this
    case without generating any actual code.

Of course all this applies recursively, so that we flatten out nested tuples.

Note [Unarisation and nullary tuples]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The above scheme has a special cases for nullary unboxed tuples, x :: (# #)
To see why, consider
    f2 :: (# Int, Int #) -> Int
    f1 :: (# Int #) -> Int
    f0 :: (# #) -> Int

When we "unarise" to eliminate unboxed tuples (this is done at the STG level),
we'll transform to
    f2 :: Int -> Int -> Int
    f1 :: Int -> Int
    f0 :: ??

We do not want to give f0 zero arguments, otherwise a lambda will
turn into a thunk! So we want to get
    f0 :: Void# -> Int

So here is what we do for nullary tuples

  * Extend the UnariseEnv with   x :-> [voidPrimId]

  * Replace bindings with a binding for void:Void#
       \x. e  =>  \void. e
    and similarly case alternatives

  * If we find (# #) as an argument all by itself
       f ...(# #)...
    it looks like an Id, so we look up in UnariseEnv. We want to replace it
    with voidPrimId, so the convenient thing is to initalise the UnariseEnv
    with   (# #) :-> [voidPrimId]

See also Note [Nullary unboxed tuple] in Type.hs.

Note [Unarisation and arity]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Because of unarisation, the arity that will be recorded in the generated info table
for an Id may be larger than the idArity. Instead we record what we call the RepArity,
which is the Arity taking into account any expanded arguments, and corresponds to
the number of (possibly-void) *registers* arguments will arrive in.
-}

{-# LANGUAGE CPP, TupleSections #-}

module UnariseStg (unarise) where

#include "HsVersions.h"

import BasicTypes
import CoreSyn
import DataCon
import FastString (FastString, mkFastString)
import Id
import MkId ( voidPrimId )
import Literal (Literal (..))
import MkCore (rUNTIME_ERROR_ID)
import MonadUtils (mapAccumLM)
import Outputable
import StgSyn
import TyCon
import Type
import TysPrim (intPrimTy, intPrimTyCon)
import TysWiredIn
import UniqSupply
import Util
import VarEnv

import Data.Bifunctor (second)
import Data.List (partition)
import Data.Maybe (fromMaybe)

import ElimUbxSums

-- | A mapping from unboxed-tuple binders to the Ids they were expanded to.
--
-- INVARIANT: Ids in the range don't have unboxed tuple types.
--
-- Those in-scope variables without unboxed-tuple types are not present in
-- the domain of the mapping at all.
type UnariseEnv = VarEnv [Id]

unarise :: UniqSupply -> [StgBinding] -> [StgBinding]
unarise us binds = initUs_ us (mapM (unariseBinding init_env) binds)
  where
     -- See Note [Unarisation and nullary tuples]
     nullary_tup = dataConWorkId unboxedUnitDataCon
     init_env = unitVarEnv nullary_tup [voidPrimId]

unariseBinding :: UnariseEnv -> StgBinding -> UniqSM StgBinding
unariseBinding rho (StgNonRec x rhs) =
    StgNonRec x <$> unariseRhs rho rhs
unariseBinding rho (StgRec xrhss)    =
    StgRec <$> mapM (\(x, rhs) -> (x,) <$> unariseRhs rho rhs) xrhss

unariseRhs :: UnariseEnv -> StgRhs -> UniqSM StgRhs
unariseRhs rho (StgRhsClosure ccs b_info fvs update_flag args expr body_ty)
  = do (rho', args') <- unariseIdBinders rho args
       expr' <- unariseExpr rho' expr body_ty
       return (StgRhsClosure ccs b_info (unariseIds rho fvs) update_flag args' expr' body_ty)

unariseRhs rho (StgRhsCon ccs con args)
  = return (StgRhsCon ccs con (unariseArgs rho args))

------------------------
unariseExpr :: UnariseEnv -> StgExpr -> Type -> UniqSM StgExpr
unariseExpr rho (StgApp f args) ty
  | null args
  , UbxTupleRep tys <- repType (idType f)
  =  -- Particularly important where (##) is concerned
     -- See Note [Nullary unboxed tuple]
    return (StgConApp (tupleDataCon Unboxed (length tys))
                      (map StgVarArg (unariseId rho f)))

  | null args
  , Just (tycon, ty_args) <- splitTyConApp_maybe ty
  , isUnboxedSumTyCon tycon
  , (ubx_fields, bx_fields) <- unboxedSumTyConFields (dropRuntimeRepArgs ty_args)
  , (ubx_args, bx_args) <- partition (isUnliftedType . idType) (unariseId rho f)
  = return (StgConApp (tupleDataCon Unboxed (ubx_fields + bx_fields))
                      (map StgVarArg ubx_args ++
                       replicate (ubx_fields - length ubx_args) uBX_DUMMY_ARG ++
                       map StgVarArg bx_args ++
                       replicate (bx_fields - length bx_args) bX_DUMMY_ARG))

  -- We now use rho for renaming too
  | Just [f'] <- lookupVarEnv rho f
  = return (StgApp f' (unariseArgs rho args))

  | otherwise
  = return (StgApp f (unariseArgs rho args))

unariseExpr _ (StgLit l) _
  = return (StgLit l)

unariseExpr rho (StgConApp dc args) ty
  | isUnboxedTupleCon dc
  , let args' = unariseArgs rho args
  = return (StgConApp (tupleDataCon Unboxed (length args')) args')

  | isUnboxedSumCon dc
  , ASSERT2(isUnboxedSumType ty, ppr ty $$ ppr dc) True
  , (tycon, ty_args) <- splitTyConApp ty
  , ASSERT2(isUnboxedSumTyCon tycon, ppr ty $$ ppr tycon $$ ppr dc) True
  , (ubx_fields, bx_fields) <- unboxedSumTyConFields (dropRuntimeRepArgs ty_args)
  , let args' = unariseArgs rho (filter (not . isNullaryTupleArg) args)
  , (ubx_args, bx_args) <- partition (isUnliftedType . stgArgType) args'
  , let tag = dataConTag dc
  = return (StgConApp (tupleDataCon Unboxed (ubx_fields + bx_fields))
                      (mkTagArg tag :
                       ubx_args ++ replicate (ubx_fields - length ubx_args - 1) uBX_DUMMY_ARG ++
                       bx_args ++ replicate (bx_fields - length bx_args) bX_DUMMY_ARG))

  | otherwise
  = return (StgConApp dc (unariseArgs rho args))

unariseExpr rho (StgOpApp op args ty) _
  = return (StgOpApp op (unariseArgs rho args) ty)

unariseExpr _ e@StgLam{} _
  = pprPanic "unariseExpr: found lambda" (ppr e)

unariseExpr rho (StgCase e bndr alt_ty alts) ty
  = do e' <- unariseExpr rho e (idType bndr)
       alts' <- unariseAlts rho alt_ty bndr alts ty
       return (StgCase e' bndr alt_ty' alts')
 where
    alt_ty' = case alt_ty of
                UbxSumAlt ubx_fields bx_fields -> UbxTupAlt (ubx_fields + bx_fields)
                _ -> alt_ty

unariseExpr rho (StgLet bind e) ty
  = StgLet <$> unariseBinding rho bind <*> unariseExpr rho e ty

unariseExpr rho (StgLetNoEscape bind e) ty
  = StgLetNoEscape <$> unariseBinding rho bind <*> unariseExpr rho e ty

unariseExpr rho (StgTick tick e) ty
  = StgTick tick <$> unariseExpr rho e ty

------------------------
unariseAlts :: UnariseEnv -> AltType -> Id -> [StgAlt] -> Type -> UniqSM [StgAlt]
unariseAlts rho (UbxTupAlt n) bndr [(DEFAULT, [], e)] ty
  = do (rho', ys) <- unariseIdBinder rho bndr
       e' <- unariseExpr rho' e ty
       return [(DataAlt (tupleDataCon Unboxed n), ys, e')]

unariseAlts rho (UbxTupAlt n) bndr [(DataAlt _, ys, e)] ty
  = do (rho', ys') <- unariseIdBinders rho ys
       let rho'' = extendVarEnv rho' bndr ys'
       e' <- unariseExpr rho'' e ty
       return [(DataAlt (tupleDataCon Unboxed n), ys', e')]

unariseAlts _ (UbxTupAlt _) _ alts _
  = pprPanic "unariseExpr: strange unboxed tuple alts" (ppr alts)

unariseAlts rho (UbxSumAlt ubx_fields bx_fields) bndr alts ty
  = do (rho_sum_bndrs, ys) <- unariseIdBinder rho bndr
       ASSERT(length ys == ubx_fields + bx_fields) (return ())
       let
         (tag_bndr : ubx_ys, bx_ys) = splitAt ubx_fields ys

         mkAlt :: StgAlt -> UniqSM StgAlt
         mkAlt (DEFAULT, _, e) =
           ( DEFAULT, [], ) <$> unariseExpr rho_sum_bndrs e ty

         mkAlt (DataAlt sumCon, bs, e) = do
           (rho_alt_bndrs, bs') <- unariseIdBinders rho_sum_bndrs bs
           let
             (ubx_bs, bx_bs) = partition (isUnliftedType . idType) bs'
             rns = zip ubx_bs ubx_ys ++ zip bx_bs bx_ys

             rho_alt_bndrs_renamed =
               flip mapVarEnv rho_alt_bndrs $ \vals ->
                 map (\val -> fromMaybe val (lookup val rns)) vals

             rho_alt_bndrs_orig_bndr_added =
               extendVarEnvList rho_alt_bndrs_renamed (map (second (:[])) rns)

           ret <- unariseExpr rho_alt_bndrs_orig_bndr_added e ty

           return ( LitAlt (MachInt (fromIntegral (dataConTag sumCon))), [], ret )

         mkAlt alt@(LitAlt{}, _, _) = pprPanic "unariseAlts.mkAlt" (ppr alt)

       inner_case <-
         StgCase (StgApp tag_bndr []) tag_bndr
                 (PrimAlt intPrimTyCon) . mkDefaultAlt <$> mapM mkAlt alts

       return [(DataAlt (tupleDataCon Unboxed (ubx_fields + bx_fields)), ys, inner_case)]

unariseAlts rho _ _ alts ty
  = mapM (\alt -> unariseAlt rho alt ty) alts

--------------------------
unariseAlt :: UnariseEnv -> StgAlt -> Type -> UniqSM StgAlt
unariseAlt rho (con, xs, e) ty
  = do (rho', xs') <- unariseIdBinders rho xs
       (con, xs',) <$> unariseExpr rho' e ty

------------------------
unariseArgs :: UnariseEnv -> [StgArg] -> [StgArg]
unariseArgs rho = concatMap (unariseArg rho)

unariseArg :: UnariseEnv -> StgArg -> [StgArg]
unariseArg rho (StgVarArg x) = map StgVarArg (unariseId rho x)
unariseArg _   (StgLitArg l) = [StgLitArg l]

unariseIds :: UnariseEnv -> [Id] -> [Id]
unariseIds rho = concatMap (unariseId rho)

unariseId :: UnariseEnv -> Id -> [Id]
unariseId rho x
  | Just ys <- lookupVarEnv rho x
  = -- Disabling the assertion as we also use the env for renaming now.
    -- ASSERT2( case repType (idType x) of UbxTupleRep{} -> True; UbxSumRep{} -> True; _ -> False
    --        , text "unariseId: not unboxed tuple or sum" <+> ppr x <+> parens (ppr (idType x)) )
    ys

  | otherwise
  = -- ASSERT2( case repType (idType x) of UbxTupleRep{} -> False; UbxSumRep{} -> False; _ -> True
    --        , text "unariseId: was unboxed tuple or sum" <+> ppr x )
    [x]

unariseIdBinders :: UnariseEnv -> [Id] -> UniqSM (UnariseEnv, [Id])
unariseIdBinders rho xs = second concat <$> mapAccumLM unariseIdBinder rho xs

unariseIdBinder :: UnariseEnv -> Id -> UniqSM (UnariseEnv, [Id])
unariseIdBinder rho x =
  case repType (idType x) of
    UnaryRep _      -> return (rho, [x])

    UbxTupleRep tys
      | null tys -> do -- See Note [Unarisation and nullary tuples]
        let ys   = [voidPrimId]
            rho' = extendVarEnv rho x [voidPrimId]
        return (rho', ys)
      | otherwise -> do
        ys <- mkIds (mkFastString "tup") tys
        let rho' = extendVarEnv rho x ys
        return (rho', ys)

    UbxSumRep ubx_fields bx_fields -> do
      ASSERT(length ubx_fields > 0) (return ())
      tag <- mkSysLocalOrCoVarM (mkFastString "tag") intPrimTy
      ys1 <- mkIds (mkFastString "ubx") (replicate (length ubx_fields - 1) intPrimTy)
      ys2 <- mkIds (mkFastString "bx")  (replicate (length bx_fields) liftedAny)
      let ys = tag : ys1 ++ ys2
          rho' = extendVarEnv rho x ys
      return (rho', ys)

mkIds :: FastString -> [UnaryType] -> UniqSM [Id]
mkIds fs tys = mapM (mkSysLocalOrCoVarM fs) tys

--------------------------------------------------------------------------------

liftedAny :: Type
liftedAny = anyTypeOfKind liftedTypeKind

uBX_DUMMY_ARG :: StgArg
uBX_DUMMY_ARG = StgLitArg (MachWord 0)

bX_DUMMY_ARG :: StgArg
bX_DUMMY_ARG = StgVarArg rUNTIME_ERROR_ID

mkDefaultAlt :: [StgAlt] -> [StgAlt]
mkDefaultAlt [] = pprPanic "elimUbxSumExpr.mkDefaultAlt" (text "Empty alts")
mkDefaultAlt alts@((DEFAULT, _, _) : _) = alts
mkDefaultAlt ((LitAlt{}, [], rhs) : alts) = (DEFAULT, [], rhs) : alts
mkDefaultAlt alts = dummyDefaultAlt : alts

dummyDefaultAlt :: StgAlt
dummyDefaultAlt = (DEFAULT, [], StgApp rUNTIME_ERROR_ID [])

mkTagArg :: Int -> StgArg
mkTagArg = StgLitArg . MachInt . fromIntegral

isNullaryTupleArg :: StgArg -> Bool
isNullaryTupleArg StgLitArg{}   = False
isNullaryTupleArg (StgVarArg v) = v == dataConWorkId unboxedUnitDataCon
