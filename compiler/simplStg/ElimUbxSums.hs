{-# LANGUAGE CPP, TupleSections #-}

module ElimUbxSums
  ( typeUnboxedSumRep
  , unboxedSumTyConFields
  , unboxedSumRepTypes
  ) where

#include "HsVersions.h"

import BasicTypes
import DataCon
import Outputable
import TyCon
import Type
import TysPrim
import TysWiredIn
import Util

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif

import Data.List (partition)
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------

-- | Returns unboxed sum representation of a type. The list of cons must have
-- all data cons of the type, and should have more than one DataCon. (otherwise
-- it wouldn't be a sum type)
typeUnboxedSumRep :: [DataCon] -> [Type]
typeUnboxedSumRep cons =
    unboxedSumRepTypes (mapMaybe (mk_tup . dataConRepArgTys) cons)
  where
    mk_tup :: [Type] -> Maybe Type
    mk_tup []   = Nothing
    mk_tup [ty] = Just ty
    mk_tup tys  = Just (mkTupleTy Unboxed tys)

-- INVARIANT: Returned list doesn't have unboxed tuples or sums.
-- Includes the tag field.
unboxedSumRepTypes :: [Type] -> [Type]
unboxedSumRepTypes alts =
    let
      alt_tys = map go alts

      con_rep_tys_parts :: [([Type], [Type])]
      con_rep_tys_parts = map (partition isPrimitiveType) alt_tys

      fields_unboxed = maximum (0 : map (length . fst) con_rep_tys_parts)
      fields_boxed   = maximum (0 : map (length . snd) con_rep_tys_parts)

      go :: Type -> [Type]
      go ty
        | Just (tc, args) <- splitTyConApp_maybe ty
        , isUnboxedTupleTyCon tc
        = concatMap go (dropLevityArgs args)

        | Just (tc, args) <- splitTyConApp_maybe ty
        , isUnboxedSumTyCon tc
        = concatMap go (unboxedSumRepTypes (dropLevityArgs args))

        | isVoidTy ty
        = []

        | otherwise
        = [ty]

      ret = intPrimTy :
            replicate fields_unboxed intPrimTy ++
            replicate fields_boxed liftedAny
    in
      ASSERT(not (any isUnboxedSumType ret) && not (any isUnboxedTupleType ret))
      -- pprTrace "unboxedSumRetTypes"
      --   (text "input:" <+> ppr alts $$
      --    text "con_rep_tys_parts:" <+> ppr con_rep_tys_parts $$
      --    text "output:" <+> ppr ret) $
        ret

-- | Returns (# unboxed fields, # boxed fields) for a UnboxedSum TyCon
-- application. NOTE: Tag field is included.
unboxedSumTyConFields :: [Type] -> (Int, Int)
unboxedSumTyConFields alts =
    let
      rep_tys = unboxedSumRepTypes alts
      (ubx_tys, bx_tys) = partition isPrimitiveType rep_tys
    in
      (length ubx_tys, length bx_tys)

liftedAny :: Type
liftedAny = anyTypeOfKind liftedTypeKind
