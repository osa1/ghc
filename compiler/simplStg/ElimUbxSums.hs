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
import Util (debugIsOn, zipEqual)

import Data.List (foldl', sort)
import Data.Maybe (mapMaybe, maybeToList)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

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
  -> [StgArg]  -- Actual arguments of the alternative
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
            layout'  = layout (tail (ubxSumSlots sum_rep)) (mapMaybe (typeSlotTy . stgArgType) stg_args)
            tag_arg  = StgLitArg (MachInt (fromIntegral tag))
            arg_idxs = IM.fromList (zipEqual "mkUbxSum" layout' stg_args)

            mkTupArgs :: Int -> [SlotTy] -> IM.IntMap StgArg -> [StgArg]
            mkTupArgs _ [] _
              = []
            mkTupArgs arg_idx (slot : slots_left) arg_map
             | Just stg_arg <- IM.lookup arg_idx arg_map
             = stg_arg : mkTupArgs (arg_idx + 1) slots_left arg_map
             | otherwise
             = slotDummyArg slot : mkTupArgs (arg_idx + 1) slots_left arg_map
          in
            StgConApp (tupleDataCon Unboxed (length (ubxSumSlots sum_rep)))
                      (tag_arg : mkTupArgs 0 (tail (ubxSumSlots sum_rep)) arg_idxs)
                      (map slotTyToType (ubxSumSlots sum_rep))

-- | Given binders and arguments of a sum, maps binders to arguments for
-- renaming.
--
-- INVARIANT: We can have more arguments than binders. Example:
--
--   case x :: (# Int | Float# #) of
--     (# | f #) -> ...
--
-- Scrutinee will have this form: (# Tag#, Any, Float# #), so it'll unarise to 3
-- arguments, but we only bind one variable of type Float#.
rnUbxSumBndrs
  :: (Outputable a, Outputable b)
  => [(Type, a)] -- things we want to map to sum components
  -> [(Type, b)] -- sum components (NOT including tag)
  -> [(a, b)]
rnUbxSumBndrs bndrs args
  = ASSERT2 (length args >= length bndrs, ppr bndrs $$ ppr args)
    zipEqual "rnUbxSumBndrs" (map snd bndrs) (map (snd . (args !!)) layout')
  where
    bndr_slots = mapMaybe (typeSlotTy . fst) bndrs
    arg_slots  = mapMaybe (typeSlotTy . fst) args
    layout'    = layout arg_slots bndr_slots

layout :: [SlotTy]  -- Layout of sum. Does not include tag. The invariant of
                    -- UbxSumRepTy holds.
       -> [SlotTy]  -- Slot types of things we want to map to locations in the
                    -- sum layout
       -> [Int]     -- Where to map 'things' in the sum layout
layout sum_slots0 arg_slots0 = go arg_slots0 IS.empty
  where
    go :: [SlotTy] -> IS.IntSet -> [Int]
    go [] _
      = []
    go (arg : args) used
      = let slot_idx = findSlot arg 0 sum_slots0 used
         in slot_idx : go args (IS.insert slot_idx used)

    findSlot :: SlotTy -> Int -> [SlotTy] -> IS.IntSet -> Int
    findSlot arg slot_idx (slot : slots) useds
      | not (IS.member slot_idx useds)
      , Just slot == arg `fitsIn` slot
      = slot_idx
      | otherwise
      = findSlot arg (slot_idx + 1) slots useds
    findSlot _ _ [] _
      = pprPanic "findSlot" (text "Can't find slot" $$ ppr sum_slots0 $$ ppr arg_slots0)

--------------------------------------------------------------------------------

-- We have 3 kinds of slots:
--
--   - Pointer slot: Only shared between actual pointers to Haskell heap (i.e.
--     boxed objects)
--
--   - Word slots: Shared between IntRep, WordRep, Int64Rep, Word64Rep, AddrRep.
--
--   - Float slots: Shared between floating point types.

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
