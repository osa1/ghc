{-# LANGUAGE CPP, TupleSections #-}

module RepType
  ( -- * Code generator views onto Types
    UnaryType, RepType(..), flattenRepType, repType,
    isUnaryRep, isUnboxedTupleRep, isUnboxedSumRep,

    -- * Predicates on types
    isVoidTy, typePrimRep,

    -- * Type representation for the code generator
    typeRepArity, tyConPrimRep,

    -- * Unboxed sum representation type
    UbxSumRepTy, ubxSumFieldTypes, layout, typeSlotTy, SlotTy,
    mkUbxSumRepTy, ubxSumSlots, slotTyToType, flattenSumRep
  ) where

#include "HsVersions.h"

import BasicTypes (Arity, RepArity)
import Outputable
import PrelNames
import TyCon
import TyCoRep
import Type
import TysPrim
import TysWiredIn
import Unique (hasKey)
import Util

import Data.List (foldl', sort)
import Data.Maybe (mapMaybe, maybeToList)
import qualified Data.IntSet as IS

{- **********************************************************************
*                                                                       *
                Representation types
*                                                                       *
********************************************************************** -}

type UnaryType = Type

data RepType
  = UbxTupleRep [UnaryType] -- Represented by multiple values
                            -- Can be zero, one, or more
                            -- INVARIANT: never an empty list
                            -- (see Note [Nullary unboxed tuple])
  | UbxSumRep UbxSumRepTy
  | UnaryRep UnaryType      -- Represented by a single value

instance Outputable RepType where
  ppr (UbxTupleRep tys) = text "UbxTupleRep" <+> ppr tys
  ppr (UbxSumRep rep) = text "UbxSumRep" <+> ppr rep
  ppr (UnaryRep ty) = text "UnaryRep" <+> ppr ty

isUnaryRep :: RepType -> Bool
isUnaryRep (UnaryRep _) = True
isUnaryRep _            = False

isUnboxedTupleRep :: RepType -> Bool
isUnboxedTupleRep (UbxTupleRep _) = True
isUnboxedTupleRep _               = False

isUnboxedSumRep :: RepType -> Bool
isUnboxedSumRep (UbxSumRep _) = True
isUnboxedSumRep _             = False

flattenRepType :: RepType -> [UnaryType]
flattenRepType (UbxTupleRep tys) = tys
flattenRepType (UbxSumRep sum_rep) = flattenSumRep sum_rep
flattenRepType (UnaryRep ty) = [ty]

-- | 'repType' figure out how a type will be represented
--   at runtime.  It looks through
--
--      1. For-alls
--      2. Synonyms
--      3. Predicates
--      4. All newtypes, including recursive ones, but not newtype families
--      5. Casts
--
repType :: Type -> RepType
repType ty
  = go initRecTc ty
  where
    go :: RecTcChecker -> Type -> RepType
    go rec_nts ty                       -- Expand predicates and synonyms
      | Just ty' <- coreView ty
      = go rec_nts ty'

    go rec_nts (ForAllTy _ ty2)  -- Drop type foralls
      = go rec_nts ty2

    go rec_nts (TyConApp tc tys)        -- Expand newtypes
      | isNewTyCon tc
      , tys `lengthAtLeast` tyConArity tc
      , Just rec_nts' <- checkRecTc rec_nts tc   -- See Note [Expanding newtypes] in TyCon
      = go rec_nts' (newTyConInstRhs tc tys)

      | isUnboxedTupleTyCon tc
      = UbxTupleRep (concatMap (flattenRepType . go rec_nts) non_rr_tys)

      | isUnboxedSumTyCon tc
      = ubxSumRepType non_rr_tys
      where
          -- See Note [Unboxed tuple RuntimeRep vars] in TyCon
        non_rr_tys = dropRuntimeRepArgs tys

    go rec_nts (CastTy ty _)
      = go rec_nts ty

    go _ ty@(CoercionTy _)
      = pprPanic "repType" (ppr ty)

    go _ ty = UnaryRep ty


typeRepArity :: Arity -> Type -> RepArity
typeRepArity 0 _ = 0
typeRepArity n ty = case repType ty of
  UnaryRep (FunTy arg res) -> length (flattenRepType (repType arg)) + typeRepArity (n - 1) res
  _ -> pprPanic "typeRepArity: arity greater than type can handle" (ppr (n, ty, repType ty))

isVoidTy :: Type -> Bool
-- True if the type has zero width
isVoidTy ty = case repType ty of
                UnaryRep (TyConApp tc _) -> isUnliftedTyCon tc &&
                                            isVoidRep (tyConPrimRep tc)
                _                        -> False


{- **********************************************************************
*                                                                       *
                Unboxed sums
 See Note [Translating unboxed sums to unboxed tuples] in UnariseStg.hs
*                                                                       *
********************************************************************** -}


-- | An unboxed sum is represented as its slots. Includes the tag.
-- INVARIANT: List is sorted, except the slot for tag always comes first.
newtype UbxSumRepTy = UbxSumRepTy { ubxSumSlots :: [SlotTy] }

ubxSumFieldTypes :: UbxSumRepTy -> [Type]
ubxSumFieldTypes = map slotTyToType . ubxSumSlots

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

-- Used when unarising sum binders (need to give unarised Ids types)
slotTyToType :: SlotTy -> Type
slotTyToType PtrSlot    = anyTypeOfKind liftedTypeKind
slotTyToType Word64Slot = int64PrimTy
slotTyToType WordSlot   = intPrimTy
slotTyToType DoubleSlot = doublePrimTy
slotTyToType FloatSlot  = floatPrimTy

-- | Returns the bigger type if one fits into the other. (commutative)
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
  where
    isPtrSlot PtrSlot = True
    isPtrSlot _       = False

    isWordSlot Word64Slot = True
    isWordSlot WordSlot   = True
    isWordSlot _          = False

    isFloatSlot DoubleSlot = True
    isFloatSlot FloatSlot  = True
    isFloatSlot _          = False

--------------------------------------------------------------------------------

ubxSumRepType :: [Type] -> RepType
ubxSumRepType = UbxSumRep . mkUbxSumRepTy

flattenSumRep :: UbxSumRepTy -> [UnaryType]
flattenSumRep = map slotTyToType . ubxSumSlots

{-
%************************************************************************
%*                                                                      *
                   PrimRep
*                                                                      *
************************************************************************
-}

-- ToDo: this could be moved to the code generator, using splitTyConApp instead
-- of inspecting the type directly.

-- | Discovers the primitive representation of a more abstract 'UnaryType'
typePrimRep :: Type -> PrimRep
typePrimRep ty = kindPrimRep (typeKind ty)

-- | Find the primitive representation of a 'TyCon'. Defined here to
-- avoid module loops. Call this only on unlifted tycons.
tyConPrimRep :: TyCon -> PrimRep
tyConPrimRep tc = kindPrimRep res_kind
  where
    res_kind = tyConResKind tc

-- | Take a kind (of shape @TYPE rr@) and produce the 'PrimRep' of values
-- of types of this kind.
kindPrimRep :: Kind -> PrimRep
kindPrimRep ki | Just ki' <- coreViewOneStarKind ki = kindPrimRep ki'
kindPrimRep (TyConApp typ [runtime_rep])
  = ASSERT( typ `hasKey` tYPETyConKey )
    go runtime_rep
  where
    go rr | Just rr' <- coreView rr = go rr'
    go (TyConApp rr_dc args)
      | RuntimeRep fun <- tyConRuntimeRepInfo rr_dc
      = fun args
    go rr = pprPanic "kindPrimRep.go" (ppr rr)
kindPrimRep ki = WARN( True
                     , text "kindPrimRep defaulting to PtrRep on" <+> ppr ki )
                 PtrRep  -- this can happen legitimately for, e.g., Any


