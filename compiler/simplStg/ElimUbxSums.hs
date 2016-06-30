{-# LANGUAGE CPP, TupleSections #-}

-- | See Note [Translating unboxed sums to unboxed tuples] in UnariseStg.hs.
module ElimUbxSums
  ( isEnumUbxSum
  , mkUbxSum
  , rnUbxSumBndrs
  , ubxSumRepType
  , UbxSumRepTy
  , ubxSumFieldTypes
  , flattenSumRep
  ) where

#include "HsVersions.h"

import BasicTypes
import DataCon
import Literal
import Outputable
import StgSyn
import TyCon
import Type
import TysPrim
import TysWiredIn
import Util (debugIsOn)

import Data.List (foldl', sort, sortOn)
import Data.Maybe (mapMaybe, maybeToList)

--------------------------------------------------------------------------------

-- | An unboxed sum is represented as its slots. Includes the tag.
-- INVARIANT: List is sorted, except the slot for tag always comes first.
newtype UbxSumRepTy = UbxSumRepTy { ubxSumSlots :: [SlotTy] }

ubxSumFieldTypes :: UbxSumRepTy -> [Type]
ubxSumFieldTypes = map slotTyToType . ubxSumSlots

isEnumUbxSum :: UbxSumRepTy -> Bool
isEnumUbxSum (UbxSumRepTy [_]) = True
isEnumUbxSum _                 = False

instance Outputable UbxSumRepTy where
  ppr (UbxSumRepTy slots) = text "UbxSumRepTy" <+> ppr slots

-- | Given types of constructor arguments, return the unboxed sum rep type.
mkUbxSumRepTy :: [Type] -> UbxSumRepTy
mkUbxSumRepTy constrs0 =
  ASSERT2( length constrs0 > 1, ppr constrs0 ) -- otherwise it isn't a sum type
  let
    combine_alts
      :: [[SlotTy]]  -- slots of constructors
      -> [SlotTy]    -- final slots
    combine_alts constrs = foldl' merge [] constrs

    merge :: [SlotTy] -> [SlotTy] -> [SlotTy]
    merge existing_slots []
      = existing_slots
    merge [] needed_slots
      = needed_slots
    merge (es : ess) (s : ss)
      | Just s' <- s `fitsIn` es
      = -- found a slot, use it
        s' : merge ess ss

      | otherwise
      = -- keep searching for a slot
        es : merge ess (s : ss)

    -- Nesting unboxed tuples and sums is OK, so we need to flatten first.
    rep :: Type -> [SlotTy]
    rep ty = case repType ty of
               UbxTupleRep tys   -> sort (mapMaybe typeSlotTy tys)
               UbxSumRep sum_rep -> mapMaybe typeSlotTy (flattenSumRep sum_rep)
               UnaryRep ty'      -> maybeToList (typeSlotTy ty')

    sumRep = UbxSumRepTy (WordSlot : combine_alts (map rep constrs0))
  in
    sumRep

-- | Build a unboxed sum term from arguments of an alternative.
mkUbxSum
  :: DataCon   -- Sum data con
  -> [Type]    -- Type arguments of the sum data con
  -> [StgArg]  -- Actual arguments
  -> StgExpr
mkUbxSum dc ty_args stg_args
  = let
      sum_rep = mkUbxSumRepTy ty_args
      tag = dataConTag dc
    in
      if isEnumUbxSum sum_rep
        then
          ASSERT (null stg_args)
          StgLit (MachInt (fromIntegral tag))
        else
          let
            arg_tys = map stgArgType stg_args

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

            tup_args = StgLitArg (MachInt (fromIntegral tag)) :
                         bindFields (tail (ubxSumSlots sum_rep)) -- drop tag slot
                                    (mkSlots (zip arg_tys stg_args))
          in
            StgConApp (tupleDataCon Unboxed (length tup_args)) tup_args arg_tys

-- | Given binders and arguments of a sum, maps binders to arguments for
-- renaming.
--
-- INVARIANT: We can have more arguments than binders. Example:
--
--   case (# | 123# #) :: (# Int | Float# #) of
--     (# | f #) -> ...
--
-- Scrutinee will have this form: (# Tag#, Any, Float# #), so it'll unarise to 3
-- arguments, but we only bind one variable of type Float#.
rnUbxSumBndrs :: (Outputable a, Outputable b) => [(Type, a)] -> [(Type, b)] -> [(a, b)]
rnUbxSumBndrs bndrs args
  = ASSERT2 (length args >= length bndrs, ppr bndrs $$ ppr args)
    mapBinders bndr_slots arg_slots
  where
    bndr_slots = mkSlots bndrs
    arg_slots  = mkSlots args

    mapBinders :: [(SlotTy, a)] -> [(SlotTy, b)] -> [(a, b)]
    mapBinders [] _
      = []
    mapBinders alt_ss@((slot_ty, slot_id) : slots) ((sum_arg_ty, sum_arg) : sum_args)
      | Just slot_ty == (sum_arg_ty `fitsIn` slot_ty)
      = (slot_id, sum_arg) : mapBinders slots sum_args
      | otherwise
      = mapBinders alt_ss sum_args
    mapBinders _ _
      = pprPanic "rnUbxSumBndrs.mapBinders" (ppr bndrs $$ ppr args)

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

data SlotTy = PtrSlot | WordSlot | Word64Slot | FloatSlot | DoubleSlot
  deriving (Eq, Ord) -- Constructor order is important! We want same type of
                     -- slots with different sizes to be next to each other.

instance Outputable SlotTy where
  ppr PtrSlot    = text "PtrSlot"
  ppr Word64Slot = text "Word64Slot"
  ppr WordSlot   = text "WordSlot"
  ppr DoubleSlot = text "DoubleSlot"
  ppr FloatSlot  = text "FloatSlot"

-- Some types don't have any slots, e.g. the ones with VoidRep.
typeSlotTy :: UnaryType -> Maybe SlotTy
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
slotTyToType Word64Slot = int64PrimTy
slotTyToType WordSlot   = intPrimTy
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
ubxSumRepType = UbxSumRep . mkUbxSumRepTy

flattenSumRep :: UbxSumRepTy -> [UnaryType]
flattenSumRep = map slotTyToType . ubxSumSlots
