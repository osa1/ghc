{-# LANGUAGE CPP, TupleSections #-}

module ElimUbxSums ( elimUbxSums ) where

#include "HsVersions.h"

import BasicTypes (Boxity (..))
import CoreSyn (AltCon (..))
import DataCon
import FastString (mkFastString)
import Id (idType, mkSysLocalM, setIdType)
import Literal (Literal (..))
import Outputable
import StgSyn
import TyCon
import Type
import TypeRep (Type (..))
import TysPrim (anyTypeOfKind, intPrimTy, intPrimTyCon)
import TysWiredIn (tupleDataCon, mkTupleTy)
import UniqSet (mapUniqSet)
import UniqSupply
import VarSet (mapVarSet)

import MkCore (uNDEFINED_ID)

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif

import Control.Monad (replicateM)
import Data.List (partition)

--------------------------------------------------------------------------------
-- PROBLEM: When generating code for unboxed sum DataCon applications and
-- unboxed sum pattern matching, we don't know how the DataCon rep types are
-- instantiated. Suppose we have
--
--     let a = (# | | 10 | #) in ...
--
-- or
--
--     case x of
--       (# a | | #) -> ...
--       (# | b | #) -> ...
--       (# | | c #) -> ...
--
-- In the first case, what should be the corresponding unboxed tuple constructor?
-- We don't know, without the type information!
--
-- In the second case, similarly we don't know how many boxed and unboxed
-- arguments the unboxed tuple version of this sum will take.
--
-- NOTE: Knowing the total number doesn't help. Because we have two different
-- overlapping fields for unboxed and boxed arguments.
--
-- SOLUTION: I think we have enough type information at this point to recover
-- what we need. For the first case, we have the id type(e.g. type of 'a'). In
-- the second case, `StgCase`s scrutinee binder should have the type of x. We
-- just propagate these types and when we need to translate a unboxed sum
-- DataCon we refer to this information to figure out which unboxed sum
-- constructor to use.
--
-- NOTE: 'dataConRepArgTys' is never what we need! We should be using
-- 'dataConInstArgTys' with the type arguments.
--
-- NOTE: One thing that could help us recover the information we need is to add
-- a 'RepType' and 'AltType' for unboxed sums(we may have to do this anyway, to
-- make bytecode interpreter working -- not 100% sure about this currently).
--
-- This AltType would look like: UbxSumAlt Int Int
--
-- Then here we could just look at the AltType in StgCase and that would solve
-- the problem shown in second case above.
--
-- For the first case, I think we still need to generate some type information
-- on the way to be able to choose right unboxed tuple constructors. But do we
-- have any guarantees that we'll have the type information necessary for this?
-- I'm not sure.
--

elimUbxSums :: [StgBinding] -> UniqSM [StgBinding]
elimUbxSums = mapM elimUbxSum

elimUbxSum :: StgBinding -> UniqSM StgBinding
elimUbxSum (StgNonRec bndr rhs)
  = StgNonRec (elimUbxSumTy bndr) <$> elimUbxSumRhs rhs (idType bndr)

elimUbxSum (StgRec bndrs)
  = StgRec <$> mapM (\(bndr, rhs) -> (elimUbxSumTy bndr,) <$> elimUbxSumRhs rhs (idType bndr)) bndrs

elimUbxSumRhs :: StgRhs -> Type -> UniqSM StgRhs
elimUbxSumRhs (StgRhsClosure ccs b_info fvs update_flag srt args expr) ty
  = StgRhsClosure ccs b_info (map elimUbxSumTy fvs)
                  update_flag (elimUbxSumSRT srt) (map elimUbxSumTy args)
      <$> elimUbxSumExpr expr (Just ty)

elimUbxSumRhs (StgRhsCon ccs con args) ty
  | isUnboxedTupleCon con
  , (_, ty_args) <- splitTyConApp ty
  = return (uncurry (StgRhsCon ccs) (elimUbxConApp con args ty_args))

  | otherwise
  = return (StgRhsCon ccs con (map elimUbxSumArg args))

elimUbxSumExpr :: StgExpr -> Maybe Type -> UniqSM StgExpr
elimUbxSumExpr (StgApp v []) (Just ty)
  | isUnboxedSumType ty
  , (tycon, ty_args) <- splitTyConApp ty
  , let (fields_unboxed, fields_boxed) =
          unboxedSumTyConFields tycon ty_args
  , let ty' =
          mkTupleTy Unboxed $
            intPrimTy : replicate fields_unboxed intPrimTy
                     ++ replicate fields_boxed liftedAny
  = return (StgApp (setIdType v ty') [])

elimUbxSumExpr (StgApp v args) _
  = return (StgApp (elimUbxSumTy v) (map elimUbxSumArg args))

elimUbxSumExpr e@StgLit{} _
  = return e

elimUbxSumExpr (StgConApp con args) ty
  | isUnboxedSumCon con
  , Just (_, ty_args) <- fmap splitTyConApp ty
  = -- This can only happen in scrutinee position of case expressions.
    -- I don't like how we allow complex expressions in scrutinee position in an
    -- ANF AST. (I think this was necessary for unboxed tuples)
    return (uncurry StgConApp (elimUbxConApp con args ty_args))

  | otherwise
  = return (StgConApp con (map elimUbxSumArg args))

elimUbxSumExpr (StgOpApp op args ty) _
  = return (StgOpApp op (map elimUbxSumArg args) (elimUbxSumTy' ty))

elimUbxSumExpr (StgLam args e) _
  = -- this shouldn't happen but whatever
    StgLam (map elimUbxSumTy args) <$> elimUbxSumExpr e Nothing

elimUbxSumExpr case_@(StgCase e case_lives alts_lives bndr srt alt_ty alts) ty
  | UbxSumAlt ubx_fields bx_fields <- alt_ty
  = do e' <- elimUbxSumExpr e (Just (idType bndr))

       let bndr' = elimUbxSumTy bndr
           srt'  = elimUbxSumSRT srt

       tag_binder <- mkSysLocalM (mkFastString "tag") intPrimTy

       ubx_field_binders <-
         replicateM (ubx_fields - 1) (mkSysLocalM (mkFastString "ubx") intPrimTy)

       boxed_field_binders <-
         replicateM bx_fields (mkSysLocalM (mkFastString "bx") liftedAny)

       let args = tag_binder : ubx_field_binders ++ boxed_field_binders

       let genRns :: [Var] -> [Var] -> [Var] -> [(Var, Var)]
           genRns _ _ [] = []
           genRns ubx bx (v : vs)
             | isUnLiftedType (idType v)
             , (ubx_v : ubx_vs) <- ubx
             = (v, ubx_v) : genRns ubx_vs bx vs

             | (bx_v : bx_vs) <- bx
             = (v, bx_v) : genRns ubx bx_vs vs

             | otherwise
             = pprPanic "elimUbxSumExpr.genRns" (ppr case_)
                 -- TODO: Make sure printing the whole expression is OK here.
                 -- (I think the data is cyclic, we don't want GHC to loop in
                 -- case of a panic)

           mkConAlt (DataAlt con, bndrs, _useds, rhs) = do
                     -- TODO: we should probably make use of `_used`
             rhs' <- elimUbxSumExpr rhs ty

             let rhs_renamed =
                   foldr rnStgExpr rhs'
                         (genRns ubx_field_binders boxed_field_binders bndrs)

             (LitAlt (MachInt (fromIntegral (dataConTag con))), [], [],)
               <$> elimUbxSumExpr rhs_renamed ty -- FIXME: um, why elimExpr rhs twice?

           mkConAlt alt@(LitAlt{}, _, _, _) =
             pprPanic "elimUbxSumExpr.mkConAlt" (ppr alt)

           mkConAlt (DEFAULT, bndrs, useds, rhs) =
             (DEFAULT, bndrs, useds,) <$> elimUbxSumExpr rhs ty

           -- We always need a DEFAULT case, because we transform AlgAlts to
           -- PrimAlt here. Which means our pattern matching is never
           -- exhaustive, unless we had a DEFAULT case before this
           -- transformation. In that case we just use existing DEFAULT case.
           -- Otherwise we create a dummy DEFAULT case.
           mkDefaultAlt :: [StgAlt] -> [StgAlt]
           mkDefaultAlt [] = pprPanic "elimUbxSumExpr.mkDefaultAlt" (text "Empty alts")
           mkDefaultAlt alts@((DEFAULT, _, _, _) : _) = alts
           mkDefaultAlt alts = dummyDefaultAlt : alts

           dummyDefaultAlt = (DEFAULT, [], [], StgApp uNDEFINED_ID [])

       inner_case <-
         StgCase (StgApp tag_binder []) case_lives alts_lives tag_binder srt' (PrimAlt intPrimTyCon)
           . mkDefaultAlt <$> mapM mkConAlt alts

       let outer_case =
             -- TODO: not sure about lives parts
             StgCase e' case_lives alts_lives bndr' srt' (UbxTupAlt (length args))
               [ (DataAlt (tupleDataCon Unboxed (length args)),
                  args,
                  replicate (length args) True, -- TODO: fix this
                  inner_case) ]

       return outer_case

  | otherwise
  = do e' <- elimUbxSumExpr e (Just (idType bndr))
       alts' <- mapM elimUbxSumAlt alts
       return (StgCase e' case_lives alts_lives (elimUbxSumTy bndr) (elimUbxSumSRT srt) alt_ty alts')

elimUbxSumExpr (StgLet bind e) ty
  = StgLet <$> elimUbxSum bind <*> elimUbxSumExpr e ty

elimUbxSumExpr (StgLetNoEscape live_in_let live_in_bind bind e) ty
  = StgLetNoEscape live_in_let live_in_bind <$> elimUbxSum bind <*> elimUbxSumExpr e ty

elimUbxSumExpr (StgTick tick e) ty
  = StgTick tick <$> elimUbxSumExpr e ty

--------------------------------------------------------------------------------

elimUbxSumAlt :: StgAlt -> UniqSM StgAlt
elimUbxSumAlt (con, bndrs, uses, e)
  = (con, map elimUbxSumTy bndrs, uses,) <$> elimUbxSumExpr e Nothing

--------------------------------------------------------------------------------

elimUbxSumSRT :: SRT -> SRT
elimUbxSumSRT NoSRT = NoSRT
elimUbxSumSRT (SRTEntries ids) = SRTEntries (mapVarSet elimUbxSumTy ids)

--------------------------------------------------------------------------------

elimUbxSumArg :: StgArg -> StgArg
elimUbxSumArg (StgVarArg v)
  = StgVarArg (elimUbxSumTy v)

elimUbxSumArg arg@StgLitArg{}
  = arg

elimUbxSumTy :: Var -> Var
elimUbxSumTy x = setIdType x (elimUbxSumTy' (idType x))

elimUbxSumTy' :: Type -> Type
elimUbxSumTy' t@TyVarTy{}
  = t

elimUbxSumTy' (AppTy t1 t2)
  = AppTy (elimUbxSumTy' t1) (elimUbxSumTy' t2)

elimUbxSumTy' (TyConApp con args)
  | isUnboxedSumTyCon con
  , (ubx_fields, bx_fields) <- unboxedSumTyConFields con args
  = mkTupleTy Unboxed (intPrimTy : replicate ubx_fields intPrimTy ++ replicate bx_fields liftedAny)

  | otherwise
  = TyConApp con (map elimUbxSumTy' args)

elimUbxSumTy' (FunTy t1 t2)
  = FunTy (elimUbxSumTy' t1) (elimUbxSumTy' t2)

elimUbxSumTy' (ForAllTy var ty)
  = ForAllTy var (elimUbxSumTy' ty)

elimUbxSumTy' ty@LitTy{}
  = ty

liftedAny :: Type
liftedAny = anyTypeOfKind liftedTypeKind

--------------------------------------------------------------------------------

elimUbxConApp :: DataCon -> [StgArg] -> [Type] -> (DataCon, [StgArg])
elimUbxConApp con stg_args ty_args
  = let
      (fields_unboxed, fields_boxed) =
        unboxedSumTyConFields (dataConTyCon con) ty_args

      con_unboxed_args, con_boxed_args :: [StgArg]
      (con_unboxed_args, con_boxed_args) = partition (isUnLiftedType . stgArgType) stg_args

      tuple_con = tupleDataCon Unboxed (length new_args)
      tag_arg   = StgLitArg (MachWord (fromIntegral (dataConTag tuple_con)))

      ubx_dummy_arg = StgLitArg (MachWord 0)
      bx_dummy_arg = StgVarArg uNDEFINED_ID

      unboxed_args =
        con_unboxed_args ++ replicate (fields_unboxed - length con_unboxed_args) ubx_dummy_arg
      boxed_args   =
        con_boxed_args ++ replicate (fields_boxed - length con_boxed_args) bx_dummy_arg

      new_args = tag_arg : unboxed_args ++ boxed_args
    in
      (tuple_con, new_args)

--------------------------------------------------------------------------------

type Rn = (Var, Var)

-- Do I need to worry about capturing and shadowing here? I think every binder
-- in the program has a unique 'Unique'.

rnStgExpr :: Rn -> StgExpr -> StgExpr
rnStgExpr r (StgApp f as)
  = StgApp (rnStgVar r f) (rnStgArgs r as)

rnStgExpr _ e@StgLit{}
  = e

rnStgExpr rn (StgConApp con as)
  = StgConApp con (rnStgArgs rn as)

rnStgExpr rn (StgOpApp op args ty)
  = StgOpApp op (rnStgArgs rn args) ty

rnStgExpr rn (StgLam args body)
  = StgLam args (rnStgExpr rn body)

rnStgExpr rn (StgCase scrt case_lives alts_lives bndr srt altty alts)
  = StgCase (rnStgExpr rn scrt) (rnLives rn case_lives) (rnLives rn alts_lives)
            bndr (rnSRT rn srt) altty (rnStgAlts rn alts)

rnStgExpr rn (StgLet bind body)
  = StgLet (rnStgBinding rn bind) (rnStgExpr rn body)

rnStgExpr rn (StgLetNoEscape live_in_let live_in_bind bind e)
  = StgLetNoEscape (rnLives rn live_in_let) (rnLives rn live_in_bind) bind
                   (rnStgExpr rn e)

rnStgExpr rn (StgTick t e)
  = StgTick t (rnStgExpr rn e)

rnStgBinding :: Rn -> StgBinding -> StgBinding
rnStgBinding rn (StgNonRec bndr rhs)
  = StgNonRec bndr (rnStgRhs rn rhs)

rnStgBinding rn (StgRec bs)
  = StgRec (map (\(bndr, rhs) -> (bndr, rnStgRhs rn rhs)) bs)

rnStgRhs :: Rn -> StgRhs -> StgRhs
rnStgRhs rn (StgRhsClosure ccs b_info fvs update_flag srt args expr)
  = StgRhsClosure ccs b_info (map (rnStgVar rn) fvs) update_flag
                  (rnSRT rn srt) args (rnStgExpr rn expr)

rnStgRhs rn (StgRhsCon ccs con args)
  = StgRhsCon ccs con (rnStgArgs rn args)

rnStgArgs :: Rn -> [StgArg] -> [StgArg]
rnStgArgs = map . rnStgArg

rnStgArg :: Rn -> StgArg -> StgArg
rnStgArg rn (StgVarArg v)
  = StgVarArg (rnStgVar rn v)
rnStgArg _ a@StgLitArg{} = a

rnStgAlts :: Rn -> [StgAlt] -> [StgAlt]
rnStgAlts = map . rnStgAlt

rnStgAlt :: Rn -> StgAlt -> StgAlt
rnStgAlt rn (pat, bndrs, uses, rhs)
  = (pat, bndrs, uses, rnStgExpr rn rhs)

rnLives :: Rn -> StgLiveVars -> StgLiveVars
rnLives rn = mapUniqSet (rnStgVar rn)

rnSRT :: Rn -> SRT -> SRT
rnSRT _ NoSRT = NoSRT
rnSRT rn (SRTEntries s) = SRTEntries (mapVarSet (rnStgVar rn) s)

rnStgVar :: Rn -> Var -> Var
rnStgVar (v1, v2) v3
  | v1 == v3  = v2
  | otherwise = v3
