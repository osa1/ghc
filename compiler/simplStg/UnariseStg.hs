{-
(c) The GRASP/AQUA Project, Glasgow University, 1992-2012


Note [Unarisation]
~~~~~~~~~~~~~~~~~~
The idea of this pass is to translate away *all* unboxed-tuple and unboxed-sum
binders. So for example:

  f (x :: (# Int, Bool #)) = f x + f (# 1, True #)

  ==>

  f (x1 :: Int) (x2 :: Bool) = f x1 x2 + f 1 True

It is important that we do this at the STG level and NOT at the Core level
because it would be very hard to make this pass Core-type-preserving. In this
example the type of 'f' changes, for example.

STG fed to the code generators *must* be unarised because the code generators do
not support unboxed tuple and unboxed sum binders natively.

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
       case x of (# a,b #) -> e   ==>   case (# x1, x2 #) of (# a, b #) -> e

Of course all this applies recursively, so that we flatten out nested tuples and
sums.

Note that the last case needs attention. When we have an unboxed tuple in
scrutinee position, we can can remove the case expression, and "unarise" the
binders (i.e. the case expression binder and binders in patterns). So in the
example above:

  case x of (# a, b #) -> e

UnariseEnv must have a binding for x, and x must be expanded into two variables
(as the tuple arity is 2, otherwise the program would be ill-typed). Say it's
expanded into x1 and x2. We extend the UnariseEnv so that

  x :-> [x1,x2], a :-> x1, b :-> [x2]

and then unarise the right hand side.

Note [UnariseEnv can map to literals]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To avoid redundant case expressions when unarising unboxed sums, UnariseEnv
needs to map variables to literals too. Suppose we have this Core:

  f (# x | #)

  ==> (CorePrep)

  case (# x | #) of
    (# x1, x2 #) -> f x1 x2

  ==> (Unarise)

  case (# 1#, x #) of
    (# x1, x2 #) -> f x1 x2

If UnariseEnv only maps variables to a list of variables, we can't eliminate
this case expression. So instead we map variables to [StgArg] in UnariseEnv, and
extend the environment with

  x1 :-> [1#], x2 :-> [x]

and unarise `f x1 x2`, which gives us `f 1# x`.

In general, we can always eliminate a case expression when scrutinee is an
explicit tuple. When scrutinee is an unboxed tuple, left-hand side of case alts
can be one of these two things:

  - An unboxed tuple pattern. (note that number of binders in the pattern will
    be the same as number of arguments in the scrutinee) e.g.

      (# x1, x2, x3 #) -> ...

    Scrutinee has to be in form `(# t1, t2, t3 #)` so we just extend the
    environment with

      x1 :-> [t1], x2 :-> [t2], x3 :-> [t3]

  - A variable. e.g.

      x :-> ...

    In this case we extend the environment with

      x :-> scrutinee's arguments

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
Because of unarisation, the arity that will be recorded in the generated info
table for an Id may be larger than the idArity. Instead we record what we call
the RepArity, which is the Arity taking into account any expanded arguments, and
corresponds to the number of (possibly-void) *registers* arguments will arrive
in.
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
import MkId (voidPrimId)
import MonadUtils (mapAccumLM)
import Outputable
import StgSyn
import TyCon
import Type
import TysPrim (intPrimTyCon)
import TysWiredIn
import UniqSupply
import Util
import VarEnv

import Data.Bifunctor (second)
import Data.Maybe (fromMaybe)

import ElimUbxSums

-- | A mapping from unboxed-tuple binders to the Ids they were expanded to.
--
-- INVARIANT: Ids in the range don't have unboxed tuple types.
--
-- Those in-scope variables without unboxed-tuple types are not present in the
-- domain of the mapping at all.
--
-- See also Note [UnariseEnv can map to literals].
type UnariseEnv = VarEnv [StgArg]

unarise :: UniqSupply -> [StgBinding] -> [StgBinding]
unarise us binds = initUs_ us (mapM (unariseBinding init_env) binds)
  where
     -- See Note [Unarisation and nullary tuples]
     nullary_tup = dataConWorkId unboxedUnitDataCon
     init_env = unitVarEnv nullary_tup [StgVarArg voidPrimId]

unariseBinding :: UnariseEnv -> StgBinding -> UniqSM StgBinding
unariseBinding rho (StgNonRec x rhs)
  = StgNonRec x <$> unariseRhs rho rhs
unariseBinding rho (StgRec xrhss)
  = StgRec <$> mapM (\(x, rhs) -> (x,) <$> unariseRhs rho rhs) xrhss

unariseRhs :: UnariseEnv -> StgRhs -> UniqSM StgRhs
unariseRhs rho (StgRhsClosure ccs b_info fvs update_flag args expr body_ty)
  = do (rho', args') <- unariseIdBinders rho args
       expr' <- unariseExpr rho' expr body_ty
       let fvs' = filterIdArgs (unariseIds rho fvs) -- TODO (osa): Not sure about this
       return (StgRhsClosure ccs b_info fvs' update_flag args' expr' body_ty)

unariseRhs rho (StgRhsCon ccs con args)
  = return (StgRhsCon ccs con (unariseArgs rho args))

------------------------
unariseExpr :: UnariseEnv -> StgExpr -> Type -> UniqSM StgExpr
unariseExpr rho expr@(StgApp f args) ty
  | null args
  , UbxTupleRep tys <- repType (idType f)
  =  -- Particularly important where (##) is concerned
     -- See Note [Nullary unboxed tuple]
    return (StgConApp (tupleDataCon Unboxed (length tys))
                      (unariseId rho f))

  | null args
  , isUnboxedSumType ty
  , as <- unariseId rho f
  = -- An Id bound to an unboxed sum
    return (StgConApp (tupleDataCon Unboxed (length as)) as)

  -- Renaming
  | Just [StgVarArg f'] <- lookupVarEnv rho f
  = return (StgApp f' (unariseArgs rho args))

  -- Constant propagation, usually replaces sum tag binders with actual tags
  | Just [StgLitArg l] <- lookupVarEnv rho f
  , null args
  = return (StgLit l)

  | Just as <- lookupVarEnv rho f
  = pprPanic "unariseExpr" (text "Non-tuple or sum id mapped to multiple args:" $$
                            text "in:" <+> ppr expr $$
                            text "function is mapped to:" <+> ppr as)

  | otherwise
  = return (StgApp f (unariseArgs rho args))

unariseExpr _ (StgLit l) _
  = return (StgLit l)

unariseExpr rho (StgConApp dc args) ty
  | isUnboxedTupleCon dc
  , let args' = unariseArgs rho args
  = return (StgConApp (tupleDataCon Unboxed (length args')) args')

  | isUnboxedSumCon dc
  , (tycon, ty_args) <- splitTyConApp ty
  = ASSERT2(isUnboxedSumType ty, ppr ty $$ ppr dc)
    ASSERT2(isUnboxedSumTyCon tycon, ppr ty $$ ppr tycon $$ ppr dc)
    let
      sum_rep = mkUbxSumRepTy (map return (dropRuntimeRepArgs ty_args))
      args'   = unariseArgs rho (filter (not . isNullaryTupleArg) args)
      tag     = dataConTag dc
    in
      return (mkUbxSum sum_rep tag (map (\a -> (stgArgType a, a)) args'))

  | otherwise
  = return (StgConApp dc (unariseArgs rho args))

unariseExpr rho (StgOpApp op args ty) _
  = return (StgOpApp op (unariseArgs rho args) ty)

unariseExpr _ e@StgLam{} _
  = pprPanic "unariseExpr: found lambda" (ppr e)

unariseExpr rho expr@(StgCase e bndr alt_ty alts) ty
  = do e' <- unariseExpr rho e (idType bndr)
       case (e', alts) of
         -- Special cases when scrutinee is an explicit unboxed tuple (i.e. tuple
         -- con app). See Note [Unarisation].
         (StgConApp dc args, [(DEFAULT, [], rhs)])
           | isUnboxedTupleCon dc
           -> unariseExpr (extendVarEnv rho bndr args) rhs ty

         (StgConApp dc args, [(DataAlt _, arg_bndrs, rhs)])
           | isUnboxedTupleCon dc
           -> do (rho', arg_bndrs') <- unariseIdBinders rho arg_bndrs
                 let
                   -- renamings: we apply these to range of the rho too
                   rns :: [(Id, StgArg)]
                   rns = zipEqual "unariseExpr.rns" arg_bndrs' args

                   rho'' = extendVarEnvList (renameRhoRange rns rho') $
                             (bndr, args) : map (second return) rns

                 unariseExpr rho'' rhs ty

         -- Explicit unboxed sum. Case expression can be eliminated with a
         -- little bit extra work.
         (StgConApp dc args, alts)
           | isUnboxedTupleCon dc
           -> do -- this won't be used but we need a scrutinee binder anyway
                 tag_bndr <- mkId (mkFastString "tag") (stgArgType (head args))
                 let rho' = extendVarEnv rho bndr args

                     rubbishFail = pprPanic "unariseExpr"
                                     (text "Found rubbish in tag position of an unboxed sum." $$
                                      text "expr:" <+> ppr expr $$
                                      text "unarised scrutinee:" <+> ppr e')

                 alts' <- mapM (\alt -> mkSumAlt rho' args alt ty) alts
                 return $ StgCase (case head args of
                                     StgVarArg v -> StgApp v []
                                     StgLitArg l -> StgLit l
                                     StgRubbishArg _ -> rubbishFail)
                                  tag_bndr (PrimAlt intPrimTyCon) (mkDefaultAlt alts')

         -- General case
         _ -> do alts' <- unariseAlts rho alt_ty bndr alts ty
                 let alt_ty'
                       | UbxSumAlt sum_rep <- alt_ty
                       = UbxTupAlt (length (flattenSumRep sum_rep))
                       | otherwise
                       = alt_ty
                 return (StgCase e' bndr alt_ty' alts')

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
       let rho'' = extendVarEnv rho' bndr (map StgVarArg ys')
       e' <- unariseExpr rho'' e ty
       return [(DataAlt (tupleDataCon Unboxed n), ys', e')]

unariseAlts _ (UbxTupAlt _) _ alts _
  = pprPanic "unariseExpr: strange unboxed tuple alts" (ppr alts)

-- In this case we don't need to scrutinize the tag bit
unariseAlts rho (UbxSumAlt _) bndr [(DEFAULT, _, rhs)] ty
  = do (rho_sum_bndrs, sum_bndrs) <- unariseIdBinder rho bndr
       rhs' <- unariseExpr rho_sum_bndrs rhs ty
       return [(DataAlt (tupleDataCon Unboxed (length sum_bndrs)), sum_bndrs, rhs')]

unariseAlts rho (UbxSumAlt _) bndr alts ty
  = do (rho_sum_bndrs, scrt_bndrs@(tag_bndr : _)) <- unariseIdBinder rho bndr
       alts' <- mapM (\alt -> mkSumAlt rho_sum_bndrs (map StgVarArg scrt_bndrs) alt ty) alts
       let inner_case =
             StgCase (StgApp tag_bndr []) tag_bndr
                     (PrimAlt intPrimTyCon) (mkDefaultAlt alts')
       return [ (DataAlt (tupleDataCon Unboxed (length scrt_bndrs)),
                 scrt_bndrs,
                 inner_case) ]

unariseAlts rho _ _ alts ty
  = mapM (\alt -> unariseAlt rho alt ty) alts

-- | Make alternatives that match on the tag of a sum.
mkSumAlt :: UnariseEnv
         -> [StgArg] -- ^ sum components. should at least have the tag argument,
                     --   which always comes first.
         -> StgAlt   -- ^ original alternative with sum LHS
         -> Type     -- ^ type of RHS
         -> UniqSM StgAlt
mkSumAlt rho _ (DEFAULT, _, e) ty
  = ( DEFAULT, [], ) <$> unariseExpr rho e ty

mkSumAlt rho (_ : real_args) (DataAlt sumCon, bs, e) ty
  = do (rho', bs') <- unariseIdBinders rho bs
       let
         ys_types = map (\y -> (stgArgType y, y)) real_args
         bs_types = map (\b -> (idType b, b)) bs'
         rns = rnUbxSumBndrs bs_types ys_types
         rho'' = extendVarEnvList (renameRhoRange rns rho') (map (second return) rns)
       e' <- unariseExpr rho'' e ty
       return ( LitAlt (MachInt (fromIntegral (dataConTag sumCon))), [], e' )

mkSumAlt _ scrt alt _
  = pprPanic "mkSumAlt" (ppr scrt $$ ppr alt)

--------------------------
unariseAlt :: UnariseEnv -> StgAlt -> Type -> UniqSM StgAlt
unariseAlt rho (con, xs, e) ty
  = do (rho', xs') <- unariseIdBinders rho xs
       (con, xs',) <$> unariseExpr rho' e ty

------------------------
unariseArgs :: UnariseEnv -> [StgArg] -> [StgArg]
unariseArgs rho = concatMap (unariseArg rho)

unariseArg :: UnariseEnv -> StgArg -> [StgArg]
unariseArg rho (StgVarArg x) = unariseId rho x
unariseArg _   arg           = [arg]

unariseIds :: UnariseEnv -> [Id] -> [StgArg]
unariseIds rho = concatMap (unariseId rho)

filterIdArgs :: [StgArg] -> [Id]
filterIdArgs args = [ var | StgVarArg var <- args ]

unariseId :: UnariseEnv -> Id -> [StgArg]
unariseId rho x = fromMaybe [StgVarArg x] (lookupVarEnv rho x)

unariseIdBinders :: UnariseEnv -> [Id] -> UniqSM (UnariseEnv, [Id])
unariseIdBinders rho xs = second concat <$> mapAccumLM unariseIdBinder rho xs

unariseIdBinder :: UnariseEnv -> Id -> UniqSM (UnariseEnv, [Id])
unariseIdBinder rho x =
  case repType (idType x) of
    UnaryRep _      -> return (rho, [x])

    UbxTupleRep tys
      | null tys -> do -- See Note [Unarisation and nullary tuples]
        let ys   = [voidPrimId]
            rho' = extendVarEnv rho x [StgVarArg voidPrimId]
        return (rho', ys)
      | otherwise -> do
        ys <- mkIds (mkFastString "tup") tys
        let rho' = extendVarEnv rho x (map StgVarArg ys)
        return (rho', ys)

    UbxSumRep sumRep -> do
      ys <- mkIds (mkFastString "sumf") (ubxSumFieldTypes sumRep)
      let rho' = extendVarEnv rho x (map StgVarArg ys)
      return (rho', ys)

mkIds :: FastString -> [UnaryType] -> UniqSM [Id]
mkIds fs tys = mapM (mkId fs) tys

mkId :: FastString -> UnaryType -> UniqSM Id
mkId = mkSysLocalOrCoVarM

--------------------------------------------------------------------------------

renameRhoRange :: [(Id, StgArg)] -> UnariseEnv -> UnariseEnv
renameRhoRange rns = mapVarEnv renameRange
  where
    renameRange = map $ \arg -> case arg of
                                  StgVarArg v -> fromMaybe arg (lookup v rns)
                                  _ -> arg

--------------------------------------------------------------------------------

mkDefaultAlt :: [StgAlt] -> [StgAlt]
mkDefaultAlt [] = pprPanic "elimUbxSumExpr.mkDefaultAlt" (text "Empty alts")
mkDefaultAlt alts@((DEFAULT, _, _) : _) = alts
mkDefaultAlt ((LitAlt{}, [], rhs) : alts) = (DEFAULT, [], rhs) : alts
mkDefaultAlt alts = dummyDefaultAlt : alts

dummyDefaultAlt :: StgAlt
dummyDefaultAlt = (DEFAULT, [], StgApp rUNTIME_ERROR_ID [])

isNullaryTupleArg :: StgArg -> Bool
isNullaryTupleArg (StgVarArg v) = v == dataConWorkId unboxedUnitDataCon
isNullaryTupleArg _             = False
