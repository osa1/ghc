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
  , rnUbxSumBndrs

  , ubxSumSlots
  , ubxSumRepType
  , UbxSumRepTy
  , ubxSumFieldTypes
  , flattenSumRep
  , typeSlotTy
  ) where

#include "HsVersions.h"

import BasicTypes
import Literal
import Outputable
import StgSyn
import TyCon
import Type
import TysPrim
import TysWiredIn
import Util (debugIsOn)

import Data.List (foldl', sort, sortOn)
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------

-- | An unboxed sum is represented as its slots. Includes the tag.
-- INVARIANT: List is sorted.
-- INVARIANT: Slot for the tag is always the first in the list.
--
-- FIXME: This is causing problems when we generate fresh identifiers from slots
-- that's supposed to have different types! Should we maybe keep original types
-- of fields in the original sum type?
newtype UbxSumRepTy = UbxSumRepTy { ubxSumSlots :: [SlotTy] }

ubxSumFieldTypes :: UbxSumRepTy -> [Type]
ubxSumFieldTypes = map slotTyToType . ubxSumSlots

instance Outputable UbxSumRepTy where
  ppr (UbxSumRepTy slots) = text "UbxSumRepTy" <+> ppr slots

-- | Given types of constructor arguments, return the unboxed sum rep type.
mkUbxSumRepTy :: [[Type]] -> UbxSumRepTy
mkUbxSumRepTy constrs =
  ASSERT2( length constrs > 1, ppr constrs ) -- otherwise it isn't a sum type
  let
    combine_alts
      :: [[SlotTy]]  -- slots of constructors
      -> [SlotTy]    -- final slots
    combine_alts constrs = foldl' constr_reps [] constrs

    constr_reps :: [SlotTy] -> [SlotTy] -> [SlotTy]
    constr_reps existing_slots []
      = existing_slots
    constr_reps [] needed_slots
      = needed_slots
    constr_reps (es : ess) (s : ss)
      | Just s' <- s `fitsIn` es
      = -- found a slot, use it
        s' : constr_reps ess ss

      | otherwise
      = -- keep searching for a slot
        es : constr_reps ess (s : ss)

    -- Nesting unboxed tuples and sums is OK, so we need to flatten first.
    constr_flatten_tys :: [Type] -> [Type]
    constr_flatten_tys = concatMap (flattenRepType . repType)

    constr_slot_tys :: [Type] -> [SlotTy]
    constr_slot_tys = sort . mapMaybe typeSlotTy . constr_flatten_tys

    sumRep = UbxSumRepTy (WordSlot : combine_alts (map constr_slot_tys constrs))
  in
    -- pprTrace "mkUbxSumRepTy" (ppr sumRep) sumRep
    sumRep

-- | Build a unboxed sum term.
mkUbxSum :: UbxSumRepTy -> ConTag -> [(Type, StgArg)] -> StgExpr
mkUbxSum sumTy tag fields =
  let
    field_slots = mkSlots fields

    bindFields :: [SlotTy] -> [(SlotTy, StgArg)] -> [StgArg]
    bindFields slots []
      = -- arguments are bound, fill rest of the slots with dummy values
        map slotDummyArg slots
    bindFields [] args
      = -- we still have arguments to bind, but run out of slots
        pprPanic "mkUbxSum" (text "Run out of slots. Args left to bind:" <+> ppr args)
    bindFields (slot : slots) args0@((arg_slot, arg) : args)
      | Just arg_slot == (arg_slot `fitsIn` slot)
      = arg : bindFields slots args
      | otherwise
      = slotDummyArg slot : bindFields slots args0

    args = StgLitArg (MachInt (fromIntegral tag))
                : (bindFields (tail (ubxSumSlots sumTy)) -- drop tag slot
                              field_slots)
  in
    StgConApp (tupleDataCon Unboxed (length (ubxSumSlots sumTy)))
              args
              (map stgArgType args)

-- | Given binders and arguments of a tuple, maps binders to arguments for
-- renaming.
rnUbxSumBndrs :: Outputable a => [(Type, a)] -> [(Type, StgArg)] -> [(a, StgArg)]
rnUbxSumBndrs alt_bndrs ubx_sum_args
  = mapBinders alt_bndr_slots sum_arg_slots
  where
    alt_bndr_slots = mkSlots alt_bndrs
    sum_arg_slots  = mkSlots ubx_sum_args

    mapBinders :: [(SlotTy, a)] -> [(SlotTy, StgArg)] -> [(a, StgArg)]
    mapBinders [] _
      = []
    mapBinders _ []
      = pprPanic "rnUbxSumBndrs.mapBinders"
          (text "Run out of slots but still have args to bind." $$
           text "args:" <+> ppr ubx_sum_args $$
           text "bndrs:" <+> ppr alt_bndrs $$
           text "alt_bndr_slots:" <+> ppr alt_bndr_slots $$
           text "sum_arg_slots:" <+> ppr sum_arg_slots)
    mapBinders alt_ss@((alt_slot_ty, alt_slot_id) : alt_slots) ((sum_arg_ty, sum_arg) : sum_args)
      | Just sum_arg_ty == (sum_arg_ty `fitsIn` alt_slot_ty)
      = (alt_slot_id, sum_arg) : mapBinders alt_slots sum_args

      | otherwise
      = mapBinders alt_ss sum_args

--------------------------------------------------------------------------------

-- We have 3 kinds of slots:
--
--   - 64bit integer slots: Shared between PtrRep, IntRep, WordRep, Int64Rep,
--     Word64Rep, AddrRep.
--
--   - Word-sized integer slots: Shared between PtrRep, IntRep, WordRep,
--     AddrRep.
--
--   - Word-sized float slots: Just FloatRep.
--
--   - Double-sized float slots: Shared between FloatRep and DoubleRep.
--
-- Here's how we generate slots to use for a given sum type:
--
--   - A first pass "canonicalize" reps. For all Word-sized integer reps we
--     return WordRep, for all Float-sized reps we return FloatRep etc.
--
--   - We then sort the slots. Comparison works as follows: Float slots are
--     always smaller than integer slots. In the same category we compare sizes.
--     (e.g. DoubleRep is greater than FloatRep)

data SlotTy = PtrSlot | WordSlot | Word64Slot | FloatSlot | DoubleSlot
  deriving (Eq, Ord) -- Constructor order is important!

instance Outputable SlotTy where
  ppr PtrSlot    = text "PtrSlot"
  ppr Word64Slot = text "Word64Slot"
  ppr WordSlot   = text "WordSlot"
  ppr DoubleSlot = text "DoubleSlot"
  ppr FloatSlot  = text "FloatSlot"

-- Some types don't have any slots, e.g. the ones with VoidRep.
typeSlotTy :: Type -> Maybe SlotTy
typeSlotTy ty =
    if isVoidRep primRep then Nothing else Just (primRepSlot primRep)
  where
    primRep = typePrimRep ty

mkSlots :: [(Type, a)] -> [(SlotTy, a)]
mkSlots = sortOn fst . mapMaybe (\(ty, bndr) -> (,bndr) <$> typeSlotTy ty)

primRepSlot :: PrimRep -> SlotTy
primRepSlot VoidRep     = pprPanic "primRepSlot" (text "No slot for VoidRep")
primRepSlot PtrRep      = PtrSlot
primRepSlot IntRep      = WordSlot
primRepSlot WordRep     = WordSlot
primRepSlot Int64Rep    = Word64Slot
primRepSlot Word64Rep   = Word64Slot
primRepSlot AddrRep     = WordSlot
primRepSlot FloatRep    = FloatSlot
primRepSlot DoubleRep   = DoubleSlot
primRepSlot VecRep{}    = pprPanic "primRepSlot" (text "No slot for VecRep")

slotTyToType :: SlotTy -> Type
slotTyToType PtrSlot    = anyTypeOfKind liftedTypeKind
slotTyToType Word64Slot = word64PrimTy
slotTyToType WordSlot   = wordPrimTy
slotTyToType DoubleSlot = doublePrimTy
slotTyToType FloatSlot  = floatPrimTy

isPtrSlot :: SlotTy -> Bool
isPtrSlot PtrSlot = True
isPtrSlot _       = False

isWordSlot :: SlotTy -> Bool
isWordSlot Word64Slot = True
isWordSlot WordSlot   = True
isWordSlot _          = False

isFloatSlot :: SlotTy -> Bool
isFloatSlot DoubleSlot = True
isFloatSlot FloatSlot  = True
isFloatSlot _          = False

fitsIn :: SlotTy -> SlotTy -> Maybe SlotTy
fitsIn ty1 ty2
  | isWordSlot ty1 && isWordSlot ty2
  = Just (max ty1 ty2)

  | isFloatSlot ty1 && isFloatSlot ty2
  = Just (max ty1 ty2)

  | isPtrSlot ty1 && isPtrSlot ty2
  = Just PtrSlot

  | otherwise
  = Nothing

--------------------------------------------------------------------------------

slotDummyArg :: SlotTy -> StgArg
slotDummyArg = StgRubbishArg . slotTyToType

--------------------------------------------------------------------------------

ubxSumRepType :: [Type] -> RepType
ubxSumRepType = UbxSumRep . mkUbxSumRepTy . map return

flattenSumRep :: UbxSumRepTy -> [UnaryType]
flattenSumRep = map slotTyToType . ubxSumSlots
