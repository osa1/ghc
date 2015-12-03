{-# LANGUAGE CPP, TupleSections #-}

module ElimUbxSums ( elimUbxSums ) where

#include "HsVersions.h"

import BasicTypes (Boxity (..))
import CoreSyn (AltCon (..))
import CostCentre (noCCS)
import DataCon
import FastString (mkFastString)
import Id (idType, mkSysLocalM)
import Literal (Literal (..))
import Outputable
import StgSyn
import TyCon
import Type
import TysPrim (anyTypeOfKind, intPrimTy, intPrimTyCon)
import TysWiredIn (tupleDataCon)
import UniqSupply

import MkCore (uNDEFINED_ID)

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif

import Control.Monad (replicateM)
import Data.List (partition)

--------------------------------------------------------------------------------

elimUbxSums :: [StgBinding] -> UniqSM [StgBinding]
elimUbxSums = mapM elimUbxSum

elimUbxSum :: StgBinding -> UniqSM StgBinding
elimUbxSum (StgNonRec bndr rhs)
  = StgNonRec bndr <$> elimUbxSumRhs rhs
elimUbxSum (StgRec bndrs)
  = StgRec <$> mapM (\(bndr, rhs) -> (bndr,) <$> elimUbxSumRhs rhs) bndrs

elimUbxSumRhs :: StgRhs -> UniqSM StgRhs
elimUbxSumRhs (StgRhsClosure ccs b_info fvs update_flag srt args expr)
  = StgRhsClosure ccs b_info fvs update_flag srt args <$> elimUbxSumExpr expr

elimUbxSumRhs (StgRhsCon ccs con args)
  | isUnboxedTupleCon con
  = uncurry (StgRhsCon ccs) <$> elimUbxConApp con args

  | otherwise
  = return (StgRhsCon ccs con args)

elimUbxSumExpr :: StgExpr -> UniqSM StgExpr
elimUbxSumExpr e@StgApp{}
  = return e

elimUbxSumExpr e@StgLit{}
  = return e

elimUbxSumExpr e@(StgConApp con args)
  | isUnboxedSumCon con
  = uncurry StgConApp <$> elimUbxConApp con args

  | otherwise
  = return e

elimUbxSumExpr e@StgOpApp{}
  = return e

elimUbxSumExpr (StgLam args e)
  = -- this shouldn't happen but whatever
    StgLam args <$> elimUbxSumExpr e

elimUbxSumExpr case_@(StgCase e case_lives alts_lives bndr srt alt_ty alts)
  | isUnboxedSumType (idType bndr)
  , (tycon, _) <- splitTyConApp (idType bndr)
  = do let (ubx_fields, bx_fields) = unboxedSumTyConFields tycon

       tag_binder <- mkSysLocalM (mkFastString "tag") intPrimTy

       ubx_field_binders <-
         replicateM ubx_fields (mkSysLocalM (mkFastString "ubx") intPrimTy)

       boxed_field_binders <-
         replicateM bx_fields (mkSysLocalM (mkFastString "bx") (anyTypeOfKind liftedTypeKind))

       let args = tag_binder : ubx_field_binders ++ boxed_field_binders

       let mkLets :: [Var] -> [Var] -> [Var] -> [StgBinding]
           mkLets _ _ [] = []
           mkLets ubx bx (v : vs)
             | isPrimitiveType (idType v)
             , (ubx_v : ubx_vs) <- ubx
             = StgNonRec v (StgRhsClosure
                             noCCS
                             -- TODO: I have no idea about the UpdateFlag here
                             -- TODO: Using same SRT with the case expression.
                             noBinderInfo [ubx_v] Updatable srt [] (StgApp ubx_v []))
                 : mkLets ubx_vs bx vs

             | (bx_v : bx_vs) <- bx
             = StgNonRec v (StgRhsClosure noCCS
                            noBinderInfo [bx_v] Updatable srt [] (StgApp bx_v []))
                 : mkLets ubx bx_vs vs

             | otherwise
             = pprPanic "elimUbxSumExpr.mkLets" (ppr case_)
                 -- TODO: Make sure printing the whole expression is OK here.
                 -- (I think the data is cyclic, we don't want GHC to loop in
                 -- case of a panic)

       let mkConAlt (DataAlt con, bndrs, _useds, rhs) =
                     -- TODO: we should probably make use of `_used`
             (LitAlt (MachInt (fromIntegral (dataConTag con))), [], [],
              foldr StgLet rhs (mkLets ubx_field_binders boxed_field_binders bndrs))

           mkConAlt alt@(LitAlt{}, _, _, _) =
             pprPanic "elimUbxSumExpr.mkConAlt" (ppr alt)

           mkConAlt alt@(DEFAULT, _, _, _) = alt

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

       let outer_case =
             -- TODO: not sure about lives parts
             StgCase e case_lives alts_lives bndr srt alt_ty
               [ (DataAlt (tupleDataCon Unboxed (length args)),
                  args,
                  replicate (length args) True, -- TODO: fix this
                  inner_case) ]

           inner_case =
             StgCase (StgApp tag_binder []) case_lives alts_lives tag_binder srt (PrimAlt intPrimTyCon)
               (mkDefaultAlt (map mkConAlt alts))

       return outer_case

  | otherwise
  = do e' <- elimUbxSumExpr e
       alts' <- mapM elimUbxSumAlt alts
       return (StgCase e' case_lives alts_lives bndr srt alt_ty alts')

elimUbxSumExpr (StgLet bind e)
  = StgLet <$> elimUbxSum bind <*> elimUbxSumExpr e

elimUbxSumExpr (StgLetNoEscape live_in_let live_in_bind bind e)
  = StgLetNoEscape live_in_let live_in_bind <$> elimUbxSum bind <*> elimUbxSumExpr e

elimUbxSumExpr (StgTick tick e)
  = StgTick tick <$> elimUbxSumExpr e

--------------------------------------------------------------------------------

elimUbxSumAlt :: StgAlt -> UniqSM StgAlt
elimUbxSumAlt (con, xs, uses, e) = (con, xs, uses,) <$> elimUbxSumExpr e

--------------------------------------------------------------------------------

-- TODO: We should memoize this somehow, no need to generate same information
-- for every DataCon of a TyCon.
--
-- !!! I think we should memoize this in TycCon (maybe in AlgTyConRhs.SumTyCon) !!!
elimUbxConApp :: DataCon -> [StgArg] -> UniqSM (DataCon, [StgArg])
elimUbxConApp con args
  = let
      (fields_unboxed, fields_boxed) = unboxedSumTyConFields (dataConTyCon con)

      con_unboxed_args, con_boxed_args :: [StgArg]
      (con_unboxed_args, con_boxed_args) = partition (isPrimitiveType . stgArgType) args

      tuple_con = tupleDataCon Unboxed (length new_args)
      tag_arg   = StgLitArg (MachWord (fromIntegral (dataConTag tuple_con)))

      -- FIXME: What to put here in place of undefined?
      dummy_arg = StgLitArg (MachWord 0)

      unboxed_args =
        con_unboxed_args ++ replicate (fields_unboxed - length con_unboxed_args) dummy_arg
      boxed_args   =
        con_boxed_args ++ replicate (fields_boxed - length con_boxed_args) dummy_arg

      new_args = tag_arg : unboxed_args ++ boxed_args
    in
      pprTrace "elimUbxConApp" (ppr (tuple_con, new_args)) $ return (tuple_con, new_args)
