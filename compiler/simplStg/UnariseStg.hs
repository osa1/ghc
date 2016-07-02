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

In more detail: (see next note for unboxed sums)

Suppose that a variable x : (# t1, t2 #).

  * At the binding site for x, make up fresh vars  x1:t1, x2:t2

  * Extend the UnariseEnv   x :-> [x1,x2]

  * Replace the binding with a curried binding for x1,x2

       Lambda:   \x.e                ==>   \x1 x2. e
       Case alt: MkT a b x c d -> e  ==>   MkT a b x1 x2 c d -> e

  * Replace argument occurrences with a sequence of args via a lookup in
    UnariseEnv

       f a b x c d   ==>   f a b x1 x2 c d

  * Replace tail-call occurrences with an unboxed tuple via a lookup in
    UnariseEnv

       x  ==>  (# x1, x2 #)

    So, for example

       f x = x    ==>   f x1 x2 = (# x1, x2 #)

  * We /always/ eliminate a case expression when

       - It scrutinises an unboxed tuple or unboxed sum

       - The scrutinee is a variable (or when it is an explicit tuple, but the
         simplifier emiminates those)

    The case alterntative (there can be only one) can be one of these two
    things:

      - An unboxed tuple pattern. (note that number of binders in the pattern
        will be the same as number of arguments in the scrutinee) e.g.

          case v of x { (# x1, x2, x3 #) -> ... }

        Scrutinee has to be in form `(# t1, t2, t3 #)` so we just extend the
        environment with

          x :-> [t1,t2,t3]
          x1 :-> [t1], x2 :-> [t2], x3 :-> [t3]

      - A DEFAULT alternative. Just the same, without the bindings for x1,x2,x3

By the end of this pass, we only have unboxed tuples in return positions.
Unboxed sums are completely eliminated, see next note.

Note [Translating unboxed sums to unboxed tuples]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Unarise also eliminates unboxed sum binders, and translates unboxed sums in
return positions to unboxed tuples. We want to overlap fields of a sum when
translating it to a tuple to have efficient memory layout. When translating a
sum pattern to a tuple pattern, we need to translate it so that binders of sum
alternatives will be mapped to right arguments after the term translation. So
translation of sum DataCon applications to tuple DataCon applications and
translation of sum patterns to tuple patterns need to be in sync.

These translations work like this. Suppose we have

  (# x1 | | ... #) :: (# t1 | t2 | ... #)

remember that t1, t2 ... can be sums and tuples too. So we first generate
layouts of those. Then we "merge" layouts of each alternative, which gives us a
sum layout with best overlapping possible.

Layout of a flat type 'ty1' is just [ty1].
Layout of a tuple is just concatenation of layouts of its fields.

For layout of a sum type,

  - We first get layouts of all alternatives.
  - We sort these layouts based on their "slot types".
  - We merge all the alternatives.

For example, say we have (# (# Int#, Char #) | (# Int#, Int# #) | Int# #)

  - Layouts of alternatives: [ [Word, Ptr], [Word, Word], [Word] ]
  - Sorted: [ [Ptr, Word], [Word, Word], [Word] ]
  - Merge all alternatives together: [ Ptr, Word, Word ]

We add a slot for the tag to the first position. So our tuple type is

  (# Tag#, Any, Word#, Word# #)
  (we use Any for pointer slots)

Now, any term of this sum type needs to generate a tuple of this type instead.
The translation works by simply putting arguments to first slots that they fit
in. Suppose we had

  (# (# 42#, 'c' #) | | #)

42# fits in Word#, 'c' fits in Any, so we generate this application:

  (# 1#, 'c', 42#, rubbish #)

Another example using the same type: (# | (# 2#, 3# #) | #). 2# fits in Word#,
3# fits in Word #, so we get:

  (# 2#, rubbish, 2#, 3# #).

Note [Case of known con tag]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We need to be careful with literal substitutions. Suppose we have:

  Main.main6 :: GHC.Base.String
  [GblId] =
      \u [] (-> GHC.Base.String)
          case (#|_#) [8.1#] of sat_s75B {
            __DEFAULT -> Main.showAlt1 sat_s75B;
          };

After unarising scrutinee, this becomes:

  Main.main6 :: GHC.Base.String
  [GblId] =
      \u [] (-> GHC.Base.String)
          case (#,#) [2#, 8.1#] of sat_s75B {
            __DEFAULT -> Main.showAlt1 sat_s75B;
          };

Then we expand and rename the binder, and replace case expression with another
case, but one that has the tag as scrutinee:

  Main.main6 :: GHC.Base.String
  [GblId] =
      \u [] (-> GHC.Base.String)
          case 2# of {
            __DEFAULT -> Main.showAlt1 2# 8.1#;
          };

This case expression is now redundant.

Note [UnariseEnv can map to literals]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
To avoid redundant case expressions when unarising unboxed sums, UnariseEnv
needs to map variables to literals too. Suppose we have this Core:

  f (# x | #)

  ==> (CorePrep)

  case (# x | #) of y {
    _ -> f y
  }

  ==> (Unarise)

  case (# 1#, x #) of [x1, x2] {
    _ -> f x1 x2
  }

To eliminate this case expression we need to map x1 to 1# in UnariseEnv:

  x1 :-> [1#], x2 :-> [x]

so that `f x1 x2` becomes `f 1# x`.

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
import MonadUtils (mapAccumLM)
import Outputable
import RepType
import StgSyn
import Type
import TysPrim (intPrimTyCon, intPrimTy)
import TysWiredIn
import UniqSupply
import Util
import VarEnv (VarEnv, extendVarEnv, emptyVarEnv, lookupVarEnv)

import Data.Bifunctor (second)
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.IntMap as IM

--------------------------------------------------------------------------------

-- | A mapping from binders to the Ids they were expanded/renamed to.
--
-- INVARIANT: Ids in the range only have "unary" types. (i.e. no unboxed
--            tuples or sums)
--
type UnariseEnv = VarEnv [StgArg]

-- | Invariant checking version of `extendVarEnv`. See the UnariseEnv invariant
-- above.
extendRho :: UnariseEnv -> Id -> [StgArg] -> UnariseEnv
extendRho rho x args
  = ASSERT2 (all (isUnaryRep . repType . stgArgType) args, ppr (map (\a -> (a, stgArgType a)) args))
    extendVarEnv rho x args

--------------------------------------------------------------------------------

unarise :: UniqSupply -> [StgBinding] -> [StgBinding]
unarise us binds = initUs_ us (mapM (unariseBinding emptyVarEnv) binds)

unariseBinding :: UnariseEnv -> StgBinding -> UniqSM StgBinding
unariseBinding rho (StgNonRec x rhs)
  = StgNonRec x <$> unariseRhs rho rhs
unariseBinding rho (StgRec xrhss)
  = StgRec <$> mapM (\(x, rhs) -> (x,) <$> unariseRhs rho rhs) xrhss

unariseRhs :: UnariseEnv -> StgRhs -> UniqSM StgRhs
unariseRhs rho (StgRhsClosure ccs b_info fvs update_flag args expr body_ty)
  = do (rho', args') <- unariseIdBinders rho args
       expr' <- unariseExpr rho' expr
       let fvs' = [ v | StgVarArg v <- unariseIds rho fvs ]
       return (StgRhsClosure ccs b_info fvs' update_flag args' expr' body_ty)

unariseRhs rho (StgRhsCon ccs con args ty_args)
  = ASSERT (not (isUnboxedTupleCon con || isUnboxedSumCon con))
    return (StgRhsCon ccs con (unariseArgs rho args) ty_args)

--------------------------------------------------------------------------------

unariseExpr :: UnariseEnv -> StgExpr -> UniqSM StgExpr
unariseExpr rho (StgApp f [])
  | Just args <- unariseId rho f
  = return (mkTuple args)

unariseExpr rho (StgApp f args)
  = return (StgApp f (unariseArgs rho args))

unariseExpr _ (StgLit l)
  = return (StgLit l)

unariseExpr rho (StgConApp dc args ty_args)
  | isUnboxedTupleCon dc
  = let args' = unariseArgs rho args
     in return (mkTuple args')

  | isUnboxedSumCon dc
  = let args' = unariseArgs rho args
     in return (mkTuple (mkUbxSum dc ty_args args'))

  | otherwise
  = let args' = unariseArgs rho args
     in return (StgConApp dc args' (map stgArgType args'))

unariseExpr rho (StgOpApp op args ty)
  = return (StgOpApp op (unariseArgs rho args) ty)

unariseExpr _ e@StgLam{}
  = pprPanic "unariseExpr: found lambda" (ppr e)

unariseExpr rho (StgCase e bndr alt_ty alts)
  = do e' <- unariseExpr rho e
       unariseCase rho e' bndr alt_ty alts

unariseExpr rho (StgLet bind e)
  = StgLet <$> unariseBinding rho bind <*> unariseExpr rho e

unariseExpr rho (StgLetNoEscape bind e)
  = StgLetNoEscape <$> unariseBinding rho bind <*> unariseExpr rho e

unariseExpr rho (StgTick tick e)
  = StgTick tick <$> unariseExpr rho e

--------------------------------------------------------------------------------

unariseCase
  :: UnariseEnv
  -> StgExpr -- scrutinee, already unarised
  -> Id -> AltType -> [StgAlt] -> UniqSM StgExpr

{-
unariseCase _ scrt _ _ alts
  | pprTrace "unariseCase" (ppr scrt $$ ppr alts) False
  = undefined
-}

unariseCase rho (StgConApp con args _) bndr _ [(DEFAULT, [], rhs)]
  | isUnboxedTupleCon con -- works for both sums and products!
  = unariseExpr (extendRho rho bndr args) rhs

unariseCase rho (StgConApp con args _) bndr alt_ty [(DataAlt _, bndrs, rhs)]
  = do -- This can only happen as a result of some unarisation, otherwise
       -- simplifier would eliminate this case
       MASSERT (isUnboxedTupleCon con) -- again works for both sums and products
       let rho'
             | UbxSumAlt _ <- alt_ty
             = mapSumIdBinders (head bndrs) -- sum patterns have one binder only
                               args rho
             | otherwise
             = mapTupleIdBinders bndrs args rho

       unariseExpr (extendRho rho' bndr args) rhs

unariseCase rho scrt@(StgConApp _ args@(tag_arg : real_args) _) bndr (UbxSumAlt _) alts
  = do -- this won't be used but we need a scrutinee binder anyway
       tag_bndr <- mkId (mkFastString "tag") tagTy
       let rho' = extendRho rho bndr args

           rubbishFail = pprPanic "unariseExpr"
                           (text "Found rubbish in tag position of an unboxed sum." $$
                            text "expr:" <+> ppr tag_arg $$
                            text "unarised scrutinee:" <+> ppr scrt)

       alts' <- mapM (\alt -> unariseSumAlt rho' real_args alt) alts

       return $ case tag_arg of
         StgLitArg l ->
           -- See Note [Case of known con tag]
           selectLitAlt l alts'
         StgVarArg v ->
           StgCase (StgApp v []) tag_bndr tagAltTy (mkDefaultLitAlt alts')
         StgRubbishArg _ ->
           rubbishFail

unariseCase rho scrt bndr alt_ty alts
  = do alts' <- unariseAlts rho alt_ty bndr alts
       let alt_ty'
             | UbxSumAlt sum_rep <- alt_ty
             = translateSumAlt sum_rep
             | otherwise
             = alt_ty
       return (StgCase scrt bndr alt_ty' alts')

--------------------------------------------------------------------------------

unariseAlts :: UnariseEnv -> AltType -> Id -> [StgAlt] -> UniqSM [StgAlt]
unariseAlts rho (UbxTupAlt n) bndr [(DEFAULT, [], e)]
  = do (rho', ys) <- unariseIdBinder rho bndr
       e' <- unariseExpr rho' e
       return [(DataAlt (tupleDataCon Unboxed n), ys, e')]

unariseAlts rho (UbxTupAlt n) bndr [(DataAlt _, ys, e)]
  = do (rho', ys') <- unariseIdBinders rho ys
       let rho'' = extendRho rho' bndr (map StgVarArg ys')
       e' <- unariseExpr rho'' e
       return [(DataAlt (tupleDataCon Unboxed n), ys', e')]

unariseAlts _ (UbxTupAlt _) _ alts
  = pprPanic "unariseExpr: strange unboxed tuple alts" (ppr alts)

-- In this case we don't need to scrutinize the tag bit
unariseAlts rho (UbxSumAlt _) bndr [(DEFAULT, _, rhs)]
  = do (rho_sum_bndrs, sum_bndrs) <- unariseIdBinder rho bndr
       rhs' <- unariseExpr rho_sum_bndrs rhs
       return [(DataAlt (tupleDataCon Unboxed (length sum_bndrs)), sum_bndrs, rhs')]

unariseAlts rho (UbxSumAlt _) bndr alts
  = do (rho_sum_bndrs, scrt_bndrs@(tag_bndr : real_bndrs)) <- unariseIdBinder rho bndr
       alts' <- mapM (\alt -> unariseSumAlt rho_sum_bndrs (map StgVarArg real_bndrs) alt) alts
       let inner_case =
             StgCase (StgApp tag_bndr []) tag_bndr
                     tagAltTy (mkDefaultLitAlt alts')
       return [ (DataAlt (tupleDataCon Unboxed (length scrt_bndrs)),
                 scrt_bndrs,
                 inner_case) ]

unariseAlts rho _ _ alts
  = mapM (\alt -> unariseAlt rho alt) alts

unariseAlt :: UnariseEnv -> StgAlt -> UniqSM StgAlt
unariseAlt rho (con, xs, e)
  = do (rho', xs') <- unariseIdBinders rho xs
       (con, xs',) <$> unariseExpr rho' e

--------------------------------------------------------------------------------

-- | Make alternatives that match on the tag of a sum
-- (i.e. generate LitAlts for the tag)
unariseSumAlt :: UnariseEnv
              -> [StgArg] -- ^ sum components _excluding_ the tag bit.
              -> StgAlt   -- ^ original alternative with sum LHS
              -> UniqSM StgAlt
unariseSumAlt rho _ (DEFAULT, _, e)
  = ( DEFAULT, [], ) <$> unariseExpr rho e

unariseSumAlt rho args (DataAlt sumCon, [b], e)
  = do let rho' = mapSumIdBinders b args rho
       e' <- unariseExpr rho' e
       return ( LitAlt (MachInt (fromIntegral (dataConTag sumCon))), [], e' )

unariseSumAlt _ _ alt@(DataAlt _, _bs, _) -- bs needs to be a singleton
  = pprPanic "uanriseSumAlt" (text "Weird sum alt:" <+> ppr alt)

unariseSumAlt _ scrt alt
  = pprPanic "unariseSumAlt" (ppr scrt $$ ppr alt)

--------------------------------------------------------------------------------

unariseArg :: UnariseEnv -> StgArg -> [StgArg]
unariseArg rho (StgVarArg x) = unariseId' rho x
unariseArg _   arg           = [arg]

unariseArgs :: UnariseEnv -> [StgArg] -> [StgArg]
unariseArgs rho = concatMap (unariseArg rho)

unariseId :: UnariseEnv -> Id -> Maybe [StgArg]
unariseId rho x = lookupVarEnv rho x

unariseId' :: UnariseEnv -> Id -> [StgArg]
unariseId' rho x = fromMaybe [StgVarArg x] (unariseId rho x)

unariseIds :: UnariseEnv -> [Id] -> [StgArg]
unariseIds rho = concatMap (unariseId' rho)

-- | A version of `unariseIdBinder` for a list of Ids. Mappings from original
-- Ids to unarised Ids will be accumulated in the rho.
unariseIdBinders :: UnariseEnv -> [Id] -> UniqSM (UnariseEnv, [Id])
unariseIdBinders rho xs = second concat <$> mapAccumLM unariseIdBinder rho xs

-- | Given an Id with potentially unboxed tuple or sum type, returns its "flat"
-- representation by inventing new Ids for tuple or sum's fields. Example:
--
--   unariseIdBinder (x :: (# String, Bool #))
--   ==>
--   [x_1 :: String, x_2 :: Bool]
--
--   unariseIdBinder (x :: (# String | Bool #))
--   ==>
--   [x_1 :: Int#, x_2 :: Any] -- x_1 is the tag
--
-- Also adds a mapping from the original Id to new Ids in the rho.
--
-- Does not update rho and returns the original Id when the it doesn't need
-- unarisation.
unariseIdBinder :: UnariseEnv -> Id -> UniqSM (UnariseEnv, [Id])
unariseIdBinder rho x
  | Just tys <- unariseIdType x
  = do xs <- mkIds (mkFastString "us") tys
       return (extendRho rho x (map StgVarArg xs), xs)
  | otherwise
  = return (rho, [x])

unariseIdType :: Id -> Maybe [Type]
unariseIdType x =
  case repType (idType x) of
    UnaryRep _       -> Nothing
    UbxTupleRep tys  -> Just tys
    UbxSumRep sumRep -> Just (ubxSumFieldTypes sumRep)

unariseIdType' :: Id -> [Type]
unariseIdType' x = fromMaybe [idType x] (unariseIdType x)

mapTupleIdBinders
    :: [Id]         -- Un-processed binders of a tuple alternative
    -> [StgArg]     -- Arguments that form the tuple (after unarisation)
    -> UnariseEnv
    -> UnariseEnv
mapTupleIdBinders ids args rho0
  = let
      id_arities :: [(Id, Int)]  -- For each binder, how many values will represent it
      id_arities = map (\id -> (id, length (unariseIdType' id))) ids

      map_ids :: UnariseEnv -> [(Id, Int)] -> [StgArg] -> UnariseEnv
      map_ids rho [] _  = rho
      map_ids _   _  [] = pprPanic "mapTupleIdBinders" (ppr ids $$ ppr args)
      map_ids rho ((x, x_arity) : xs) args =
        let (x_args, args') = splitAt x_arity args
         in map_ids (extendRho rho x x_args) xs args'
    in
      ASSERT2 (sum (map snd id_arities) == length args, ppr id_arities $$ ppr args)
      map_ids rho0 id_arities args

mapSumIdBinders
  :: Id          -- Binder of a sum alternative (remember that sum patterns only
                 -- have one binder)
  -> [StgArg]    -- Arguments that form the sum (NOT including the tag)
  -> UnariseEnv
  -> UnariseEnv
mapSumIdBinders id sum_args rho
  = let
      arg_slots = mapMaybe typeSlotTy (concatMap (flattenRepType . repType . stgArgType) sum_args)
      id_slots  = mapMaybe typeSlotTy (unariseIdType' id)
      layout'   = layout arg_slots id_slots
    in
      extendVarEnv rho id [ sum_args !! i | i <- layout' ]

-- | Build a unboxed sum term from arguments of an alternative.
mkUbxSum
  :: DataCon   -- Sum data con
  -> [Type]    -- Type arguments of the sum data con
  -> [StgArg]  -- Actual arguments of the alternative
  -> [StgArg]  -- Final tuple arguments
mkUbxSum dc ty_args stg_args
  = let
      sum_rep = mkUbxSumRepTy ty_args
      tag = dataConTag dc

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
        = StgRubbishArg (slotTyToType slot) : mkTupArgs (arg_idx + 1) slots_left arg_map
    in
      tag_arg : mkTupArgs 0 (tail (ubxSumSlots sum_rep)) arg_idxs

translateSumAlt :: UbxSumRepTy -> AltType
translateSumAlt = UbxTupAlt . length . flattenSumRep

mkIds :: FastString -> [UnaryType] -> UniqSM [Id]
mkIds fs tys = mapM (mkId fs) tys

mkId :: FastString -> UnaryType -> UniqSM Id
mkId = mkSysLocalOrCoVarM

--------------------------------------------------------------------------------

mkTuple :: [StgArg] -> StgExpr
mkTuple args  = StgConApp (tupleDataCon Unboxed (length args)) args (map stgArgType args)

tagAltTy :: AltType
tagAltTy = PrimAlt intPrimTyCon

tagTy :: Type
tagTy = intPrimTy

mkDefaultLitAlt :: [StgAlt] -> [StgAlt]
mkDefaultLitAlt [] = pprPanic "elimUbxSumExpr.mkDefaultAlt" (text "Empty alts")
mkDefaultLitAlt alts@((DEFAULT, _, _) : _) = alts
mkDefaultLitAlt ((LitAlt{}, [], rhs) : alts) = (DEFAULT, [], rhs) : alts
mkDefaultLitAlt alts = pprPanic "mkDefaultLitAlt" (text "Not a lit alt:" <+> ppr alts)

selectLitAlt :: Literal -> [StgAlt] -> StgExpr
selectLitAlt l []
  = pprPanic "selectLitAlt" (ppr l)
selectLitAlt l ((LitAlt l', _, rhs) : alts)
  | l == l'   = rhs
  | otherwise = selectLitAlt l alts
selectLitAlt _ ((DEFAULT, _, rhs) : _)
  = rhs
selectLitAlt _ (alt@(DataAlt _, _, _) : _)
  = pprPanic "selectLitAlt" (text "Found DataAlt:" <+> ppr alt)
