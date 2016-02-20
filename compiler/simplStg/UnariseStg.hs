{-
(c) The GRASP/AQUA Project, Glasgow University, 1992-2012


Note [Unarisation]
~~~~~~~~~~~~~~~~~~

The idea of this pass is to translate away *all* unboxed-tuple binders. So for example:

f (x :: (# Int, Bool #)) = f x + f (# 1, True #)
 ==>
f (x1 :: Int) (x2 :: Bool) = f x1 x2 + f 1 True

It is important that we do this at the STG level and NOT at the core level
because it would be very hard to make this pass Core-type-preserving.

STG fed to the code generators *must* be unarised because the code generators do
not support unboxed tuple binders natively.


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
import Literal (Literal (..))
import MkCore (rUNTIME_ERROR_ID)
import MkId (realWorldPrimId)
import MonadUtils (mapAccumLM)
import Name
import OccName
import Outputable
import StgSyn
import TyCon
import Type
import TysPrim (intPrimTy, anyTypeOfKind, intPrimTyCon)
import TysWiredIn
import DataCon
import OccName
import Name
import UniqSupply
import Util
import VarEnv
import VarSet

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

ubxTupleId0 :: Id
ubxTupleId0 = dataConWorkId (tupleDataCon Unboxed 0)

unarise :: UniqSupply -> [StgBinding] -> [StgBinding]
unarise us binds = initUs_ us (mapM (unariseBinding init_env) binds)
  where -- See Note [Nullary unboxed tuple] in Type.hs
        init_env = unitVarEnv ubxTupleId0 [realWorldPrimId]

unariseBinding :: UnariseEnv -> StgBinding -> UniqSM StgBinding
unariseBinding rho (StgNonRec x rhs) =
    StgNonRec x <$> unariseRhs rho rhs (idType x)
unariseBinding rho (StgRec xrhss)    =
    StgRec <$> mapM (\(x, rhs) -> (x,) <$> unariseRhs rho rhs (idType x)) xrhss

unariseRhs :: UnariseEnv -> StgRhs -> Type -> UniqSM StgRhs
unariseRhs rho (StgRhsClosure ccs b_info fvs update_flag args expr) ty
  = do (rho', args') <- unariseIdBinders rho args
       StgRhsClosure ccs b_info (unariseIds rho fvs) update_flag args'
                     <$> unariseExpr rho' expr (dropFunArgs (length args) ty)

unariseRhs rho (StgRhsCon ccs con args) ty
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
  , (ubx_fields, bx_fields) <- unboxedSumTyConFields (dropLevityArgs ty_args)
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

unariseExpr rho e@(StgConApp dc args) ty
  | isUnboxedTupleCon dc
  , let args' = unariseArgs rho args
  = return (StgConApp (tupleDataCon Unboxed (length args')) args')

  | isUnboxedSumCon dc
  , (tycon, ty_args) <- splitTyConApp ty
  , (ubx_fields, bx_fields) <- unboxedSumTyConFields (dropLevityArgs ty_args)
  , let args' = unariseArgs rho args
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

unariseExpr rho case_@(StgCase e bndr alt_ty alts) ty
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
unariseAlts rho (UbxTupAlt n) bndr [(DEFAULT, [], [], e)] ty
  = do (rho', ys) <- unariseIdBinder rho bndr
       e' <- unariseExpr rho' e ty
       let uses = replicate (length ys) (not (isDeadBinder bndr))
       return [(DataAlt (tupleDataCon Unboxed n), ys, uses, e')]

unariseAlts rho (UbxTupAlt n) bndr [(DataAlt _, ys, uses, e)] ty
  = do (rho', ys', uses') <- unariseUsedIdBinders rho ys uses
       let rho'' = extendVarEnv rho' bndr ys'
       e' <- unariseExpr rho'' e ty
       return [(DataAlt (tupleDataCon Unboxed n), ys', uses', e')]

unariseAlts _ (UbxTupAlt _) _ alts _
  = pprPanic "unariseExpr: strange unboxed tuple alts" (ppr alts)

unariseAlts rho (UbxSumAlt ubx_fields bx_fields) bndr alts ty
  = do (rho_sum_bndrs, ys) <- unariseIdBinder rho bndr
       ASSERT(length ys == ubx_fields + bx_fields) (return ())
       let
         (tag_bndr : ubx_ys, bx_ys) = splitAt ubx_fields ys

         mkAlt :: StgAlt -> UniqSM StgAlt
         mkAlt (DEFAULT, _, _, e) =
           ( DEFAULT, [], [], ) <$> unariseExpr rho_sum_bndrs e ty

         mkAlt (DataAlt sumCon, bs, _, e) = do
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

           return ( LitAlt (MachInt (fromIntegral (dataConTag sumCon))), [], undefined, ret )

       inner_case <-
         StgCase (StgApp tag_bndr []) tag_bndr
                 (PrimAlt intPrimTyCon) . mkDefaultAlt <$> (mapM mkAlt alts)

       return [(DataAlt (tupleDataCon Unboxed (ubx_fields + bx_fields)), ys, undefined, inner_case)]

unariseAlts rho _ _ alts ty
  = mapM (\alt -> unariseAlt rho alt ty) alts

--------------------------
unariseAlt :: UnariseEnv -> StgAlt -> Type -> UniqSM StgAlt
unariseAlt rho (con, xs, uses, e) ty
  = do (rho', xs', uses') <- unariseUsedIdBinders rho xs uses
       (con, xs', uses',) <$> unariseExpr rho' e ty

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
    -- ASSERT2( case repType (idType x) of UbxTupleRep{} -> True; UbxSumRep{} -> True; _ -> x == ubxTupleId0
    --        , text "unariseId: not unboxed tuple or sum" <+> ppr x <+> parens (ppr (idType x)) )
    ys

  | otherwise
  = -- ASSERT2( case repType (idType x) of UbxTupleRep{} -> False; UbxSumRep{} -> False; _ -> True
    --        , text "unariseId: was unboxed tuple or sum" <+> ppr x )
    [x]

unariseUsedIdBinders :: UnariseEnv -> [Id] -> [Bool] -> UniqSM (UnariseEnv, [Id], [Bool])
unariseUsedIdBinders rho0 xs0 uses0
  = do (rho, xs_usess) <- mapAccumLM do_one rho0 (zipEqual "unariseUsedIdBinders" xs0 uses0)
       let (xs, uses) = unzip (concat xs_usess)
       return (rho, xs, uses)
  where
    do_one :: UnariseEnv -> (Id, Bool) -> UniqSM (UnariseEnv, [(Id, Bool)])
    do_one rho (x, use) = second (map (, use)) <$> unariseIdBinder rho x

unariseIdBinders :: UnariseEnv -> [Id] -> UniqSM (UnariseEnv, [Id])
unariseIdBinders rho xs = second concat <$> mapAccumLM unariseIdBinder rho xs

unariseIdBinder :: UnariseEnv -> Id -> UniqSM (UnariseEnv, [Id])
unariseIdBinder rho x =
  case repType (idType x) of
    UnaryRep _      -> return (rho, [x])
    UbxTupleRep tys -> do
      ys <- mkIds (mkFastString "tup") tys
      let rho' = extendVarEnv rho x ys
      return (rho', ys)
    UbxSumRep ubx_fields bx_fields -> do
      ys1 <- mkIds (mkFastString "ubx") (replicate (length ubx_fields) intPrimTy)
      ys2 <- mkIds (mkFastString "bx")  (replicate (length bx_fields) liftedAny)
      let ys = ys1 ++ ys2
          rho' = extendVarEnv rho x ys
      return (rho', ys)

mkIds :: FastString -> [UnaryType] -> UniqSM [Id]
mkIds fs tys = mapM (mkSysLocalOrCoVarM fs) tys

concatMapVarSet :: (Var -> [Var]) -> VarSet -> VarSet
concatMapVarSet f xs = mkVarSet [x' | x <- varSetElems xs, x' <- f x]

--------------------------------------------------------------------------------

liftedAny :: Type
liftedAny = anyTypeOfKind liftedTypeKind

uBX_DUMMY_ARG :: StgArg
uBX_DUMMY_ARG = StgLitArg (MachWord 0)

bX_DUMMY_ARG :: StgArg
bX_DUMMY_ARG = StgVarArg rUNTIME_ERROR_ID

mkDefaultAlt :: [StgAlt] -> [StgAlt]
mkDefaultAlt [] = pprPanic "elimUbxSumExpr.mkDefaultAlt" (text "Empty alts")
mkDefaultAlt alts@((DEFAULT, _, _, _) : _) = alts
-- mkDefaultAlt ((LitAlt{}, [], [], rhs) : alts) = (DEFAULT, [], [], rhs) : alts
mkDefaultAlt alts = dummyDefaultAlt : alts

dummyDefaultAlt :: StgAlt
dummyDefaultAlt = (DEFAULT, [], [], StgApp rUNTIME_ERROR_ID [])

dropFunArgs :: Int -> Type -> Type
dropFunArgs 0 ty = ty
dropFunArgs n ty
  | [ty'] <- flattenRepType (repType ty)
  , (bs, ty'') <- splitPiTys (dropForAlls ty')
  = ASSERT2(not (null bs), text "fun ty:" <+> ppr ty <+> text "trying to drop:" <+> ppr n)
    dropFunArgs (n - 1) (mkForAllTys (tail bs) ty'')
dropFunArgs n ty = pprPanic "dropFunArgs" (ppr n $$ ppr ty)

mkTagArg :: Int -> StgArg
mkTagArg = StgLitArg . MachInt . fromIntegral
