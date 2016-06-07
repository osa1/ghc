{-# LANGUAGE CPP, TupleSections #-}

-- | Here we implement all the tools we need to
--
--   1. Generate unboxed sum type of a sum type. (to be used in e.g.
--      implementation of UNPACK for sum types)
--
--   2. Translate unboxed sums to unboxed tuples in stg2stg.
--
module ElimUbxSums
  ( mkUbxSumRepTy
  , mkUbxSum
  , ubxSumSlots
  , ubxSumRepType
  , UbxSumRepTy
  , ubxSumFieldTypes
  , flattenSumRep
  ) where

#include "HsVersions.h"

import BasicTypes
import Literal
import MkCore (rUNTIME_ERROR_ID)
import Outputable
import StgSyn
import TyCon
import Type
import TysPrim
import TysWiredIn
import Util (debugIsOn)

import Data.List (foldl', sort, sortOn)

--------------------------------------------------------------------------------

-- | An unboxed sum is represented as its slots. Includes the tag.
-- INVARIANT: List is sorted.
newtype UbxSumRepTy = UbxSumRepTy { ubxSumSlots :: [PrimRep] }

ubxSumFieldTypes :: UbxSumRepTy -> [Type]
ubxSumFieldTypes = map primRepType . ubxSumSlots

instance Outputable UbxSumRepTy where
  ppr (UbxSumRepTy slots) = text "UbxSumRepTy" <+> ppr slots

-- | Given types of constructor arguments, return the unboxed sum type.
mkUbxSumRepTy :: [[Type]] -> UbxSumRepTy
mkUbxSumRepTy constrs =
  ASSERT( length constrs > 1 ) -- otherwise it isn't a sum type
  let
    combine_alts
      :: [[PrimRep]]  -- constructors
      -> [PrimRep]    -- final slots
    combine_alts constrs = foldl' constr_reps [] constrs

    constr_reps :: [PrimRep] -> [PrimRep] -> [PrimRep]
    constr_reps existing_reps [] = existing_reps
    constr_reps existing_reps (r : rs)
      | Just existing_reps' <- consume_rep_slot r existing_reps
      = r : constr_reps existing_reps' rs
      | otherwise
      = r : constr_reps existing_reps rs

    -- | TODO: document me
    consume_rep_slot :: PrimRep -> [PrimRep] -> Maybe [PrimRep]
    consume_rep_slot r (r' : rs)
      | r == r'
      = Just rs -- found a slot, use it and return the rest
      | otherwise
      = (r' :) <$> consume_rep_slot r rs -- keep searching for a slot
    consume_rep_slot _ []
      = Nothing -- couldn't find a slot for this rep

    -- Nesting unboxed tuples and sums is OK, so we need to flatten first.
    constr_flatten_tys :: [Type] -> [Type]
    constr_flatten_tys fields = concatMap (flattenRepType . repType) fields

    -- No need to allocate VoidRep slots as those types are simply not available
    -- in runtime.
    filter_voids :: [PrimRep] -> [PrimRep]
    filter_voids = filter (not . isVoidRep)

    constr_rep_tys :: [Type] -> [PrimRep]
    constr_rep_tys = filter_voids . map typePrimRep . constr_flatten_tys
  in
    UbxSumRepTy (IntRep : sort (combine_alts (map constr_rep_tys constrs)))

mkUbxSum :: UbxSumRepTy -> ConTag -> [(PrimRep, StgArg)] -> StgExpr
mkUbxSum sumTy tag fields =
  let
    sorted_fields = sortOn fst fields

    bindFields :: [PrimRep] -> [(PrimRep, StgArg)] -> [StgArg]
    bindFields reps []
      = -- arguments are bound, fill rest of the slots with dummy values
        map repDummyArg reps
    bindFields [] args
      = -- we still have arguments to bind, but run out of slots
        pprPanic "mkUbxSum" (text "Run out of slots. Args left to bind:" <+> ppr args)
    bindFields reps0@(rep : reps) args0@((arg_rep, arg) : args)
      | rep == arg_rep
      = arg : bindFields reps args
      | rep < arg_rep
      = repDummyArg rep : bindFields reps args0
      | otherwise
      = pprPanic "mkUbxSum" (text "Can't bind arg with rep" <+> ppr arg_rep $$
                             text "Slots left:" <+> ppr reps0 $$
                             text "sum ty:" <+> ppr sumTy $$
                             text "tag:" <+> ppr tag $$
                             text "fields:" <+> ppr fields)
  in
    StgConApp (tupleDataCon Unboxed (length (ubxSumSlots sumTy)))
              (StgLitArg (MachInt (fromIntegral tag))
                : (bindFields (tail (ubxSumSlots sumTy)) sorted_fields))

primRepType :: PrimRep -> Type
primRepType VoidRep   = voidPrimTy
primRepType PtrRep    = anyTypeOfKind liftedTypeKind
primRepType IntRep    = intPrimTy
primRepType WordRep   = wordPrimTy
primRepType Int64Rep  = int64PrimTy
primRepType Word64Rep = word64PrimTy
primRepType AddrRep   = addrPrimTy
primRepType FloatRep  = floatPrimTy
primRepType DoubleRep = doublePrimTy
primRepType VecRep{}  = error "primRepType: VecRep not supported yet"

repDummyArg :: PrimRep -> StgArg
repDummyArg VoidRep   = error "repDummyArg: VoidRep"
repDummyArg PtrRep    = StgVarArg rUNTIME_ERROR_ID
repDummyArg IntRep    = StgLitArg (MachInt 0)
repDummyArg WordRep   = StgLitArg (MachWord 0)
repDummyArg Int64Rep  = StgLitArg (MachInt64 0)
repDummyArg Word64Rep = StgLitArg (MachWord64 0)
repDummyArg AddrRep   = error "repDummyArg: AddrRep" -- FIXME: Need a MachLabel here...
repDummyArg FloatRep  = StgLitArg (MachFloat 0.0)
repDummyArg DoubleRep = StgLitArg (MachDouble 0.0)
repDummyArg VecRep{}  = error "repDummyArg: Found VecRep"

--------------------------------------------------------------------------------

ubxSumRepType :: [Type] -> RepType
ubxSumRepType = UbxSumRep . mkUbxSumRepTy . map return

flattenSumRep :: UbxSumRepTy -> [UnaryType]
flattenSumRep = map primRepType . ubxSumSlots
