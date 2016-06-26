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

  * Replace argument occurrences with a sequence of args via a lookup in
    UnariseEnv

       f a b x c d   ==>   f a b x1 x2 c d

  * Replace tail-call occurrences with an unboxed tuple via a lookup in
    UnariseEnv

       x  ==>  (# x1, x2 #)

    So, for example

       f x = x    ==>   f x1 x2 = (# x1, x2 #)

    This applies to case scrutinees too

       case x of (# a,b #) -> e   ==>   case (# x1, x2 #) of (# a, b #) -> e

    Now the case expression is redundant. When a case scrutinee becomes an
    explicit tuple after unarise, we eliminate the case expression altogether.
    So in the example above, we extend the UnariseEnv so that

      x :-> [x1,x2], a :-> x1, b :-> [x2]

    and then unarise the right hand side.

    Note that simplifier already simplifies case expressions with known
    constructors, either by choosing a case alternative, or by binding scrutinee
    in a let (this is possible because DataCon applications are OK for
    speculation). So here we only simplify cases on tuples that we introduce as
    a result of unarisation.

    In general, we can always eliminate a case expression when scrutinee is an
    explicit tuple. When scrutinee is an unboxed tuple, left-hand side of case
    alts can be one of these two things:

      - An unboxed tuple pattern. (note that number of binders in the pattern
        will be the same as number of arguments in the scrutinee) e.g.

          (# x1, x2, x3 #) -> ...

        Scrutinee has to be in form `(# t1, t2, t3 #)` so we just extend the
        environment with

          x1 :-> [t1], x2 :-> [t2], x3 :-> [t3]

      - A variable. e.g.

          x :-> ...

        In this case we extend the environment with

          x :-> scrutinee's arguments

By the end of this pass, we only have unboxed tuples in return positions.

Note [Two-step binder substitution for sums]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Explicit unboxed sums in scrutinee positions are also eliminated, however the
process is a bit more complicated. Suppose we have this:

  type Sum = (# (# Int#, Int #) | (# Int, Int# #) #)

  showP1 :: (# Int#, Int #) -> String
  showP1 = ...

  showSum :: Sum -> String
  showSum (# p1 | #) = showP1 p1
  ...

  showSum (# (# 123#, 456 #) | #)

Tuple representation of Sum will be (# Int#, Any, Int# #). Now, this is the STG for showSum:

  showSum s =
    case s of
      (# p1 | #) -> showP1 p1
      ...

We unarise s and it gives us this mapping

  (0) s :-> [s_1 :: Int#, s_2 :: Any, s_3 :: Int#]

so showSum becomes (after some simplifications)

  showSum s_1 s_2 s_3 =
    case s_1 of
      1# -> showP1 <unarisation of p1>

What will unarisation of p1 be? Note that in our tuple representation Any comes
before Int#, but in the tuple of first alternative, (# Int#, Any #), Int# comes
before Any. So correct unarisation of p1 is

  (1) p1 :-> [s_3 :: Int#, s_2 :: Any]

How do we generate this? There's an easy way. Suppose we added (0) to rho. We
unarise p1 and it gives us

  (2) p1 :-> [p1_1 :: Int#, p1_2 :: Any]

Now we map [p_1 :: Int#, p_2 :: Any] to [s_2 :: Any, s_3 :: Int#] (in
`rnUbxSumBndrs`) as described in Note [Translating unboxed sums to unboxed
tuples], that gives us

  (3) p1_1 :-> [s_3], p1_2 :-> [s_2]

Now we apply the renaming (3) to range of (2), to get (1). Then add it to the
rho.

Note [Case of known con tag]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We need to be careful with the literal substitutions. Suppose we have:

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
          case 2# of x, y {
            __DEFAULT -> Main.showAlt1 2# 8.1#;
          };

This case expression is now redundant.

Note [UnariseEnv can map to literals]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
To avoid redundant case expressions when unarising unboxed sums, UnariseEnv
needs to map variables to literals too. Suppose we have this Core:

  f (# x | #)

  ==> (CorePrep)

  case (# x | #) of
    y -> f y

  ==> (Unarise)

  case (# 1#, x #) of
    (# x1, x2 #) -> f x1 x2

To eliminate this case expression we need to map x1 to 1# in UnariseEnv:

  x1 :-> [1#], x2 :-> [x]

so that `f x1 x2` becomes `f 1# x`.

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
import MkId (voidPrimId)
import MonadUtils (mapAccumLM)
import Outputable
import StgSyn
import Type
import TysPrim (intPrimTyCon, voidPrimTy, intPrimTy)
import TysWiredIn
import UniqSupply
import Util
import VarEnv

import Data.Bifunctor (second)
import Data.Maybe (fromMaybe, fromJust)
import qualified Data.IntMap as IM

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
       expr' <- unariseExpr rho' expr
       let fvs' = filterIdArgs (unariseIds rho fvs) -- TODO (osa): Not sure about this
                  -- I think this makes sense. if a free variable became a
                  -- literal then it's not a free variable anymore.
       return (StgRhsClosure ccs b_info fvs' update_flag args' expr' body_ty)

unariseRhs rho (StgRhsCon ccs con args ty_args)
  = ASSERT (not (isUnboxedTupleCon con || isUnboxedSumCon con))
    return (StgRhsCon ccs con (unariseArgs rho args) ty_args)

------------------------
unariseExpr :: UnariseEnv -> StgExpr -> UniqSM StgExpr
unariseExpr rho (StgApp f [])
  = case unariseId rho f of
      [StgVarArg v] -> return (StgApp v []) -- renaming
      [StgLitArg l] -> return (StgLit l)    -- constant propagation. usually just for unboxed sum tags.
      args          -> return (StgConApp (tupleDataCon Unboxed (length args)) args (map stgArgType args))
                                            -- actual unarisation

unariseExpr rho (StgApp f args)
  | [StgVarArg f'] <- unariseId rho f
  = return (StgApp f' (unariseArgs rho args))

unariseExpr rho expr@(StgApp f _)
  = pprPanic "unariseExpr" (text "Tuple applied to arguments." $$
                            text "expr:" <+> ppr expr $$
                            text "unarised fun:" <+> ppr (unariseId rho f))

unariseExpr _ (StgLit l)
  = return (StgLit l)

unariseExpr rho (StgConApp dc args ty_args)
  | isUnboxedTupleCon dc
  = let args' = unariseArgs rho args
     in return (StgConApp (tupleDataCon Unboxed (length args')) args' (map stgArgType args'))

  | isUnboxedSumCon dc
  = let args' = unariseArgs rho (filter (not . isNullaryTupleArg) args)
     in return (mkUbxSum dc ty_args args')

  | otherwise
  = let args' = unariseArgs rho args
     in return (StgConApp dc args' (map stgArgType args'))

unariseExpr rho (StgOpApp op args ty)
  = return (StgOpApp op (unariseArgs rho args) ty)

unariseExpr _ e@StgLam{}
  = pprPanic "unariseExpr: found lambda" (ppr e)

unariseExpr rho expr@(StgCase e bndr alt_ty alts)
  = do e' <- unariseExpr rho e
       case (e', alts) of
         -- Special cases when scrutinee is an explicit unboxed tuple (i.e. tuple
         -- con app). See Note [Unarisation].
         (StgConApp _ args _, [(DEFAULT, [], rhs)])
           | UbxTupAlt _ <- alt_ty
           -> unariseExpr (extendVarEnv rho bndr args) rhs

         (StgConApp _ args _, [(DataAlt _, arg_bndrs, rhs)])
           | UbxTupAlt _ <- alt_ty
           -> do let rho' = extendVarEnv (mapTupleIdBinders arg_bndrs args rho) bndr args
                 unariseExpr rho' rhs

         -- Explicit unboxed sum. Case expression can be eliminated with a
         -- little bit extra work.
         (StgConApp _ args@(tag_arg : real_args) _, alts)
           | UbxSumAlt _ <- alt_ty
           -> do -- this won't be used but we need a scrutinee binder anyway
                 tag_bndr <- mkId (mkFastString "tag") tagTy
                 let rho' = extendVarEnv rho bndr args

                     rubbishFail = pprPanic "unariseExpr"
                                     (text "Found rubbish in tag position of an unboxed sum." $$
                                      text "expr:" <+> ppr expr $$
                                      text "unarised scrutinee:" <+> ppr e')

                 alts' <- mapM (\alt -> unariseSumAlt rho' real_args alt) alts

                 return $ case tag_arg of
                   StgLitArg l ->
                     -- See Note [Case of known con tag]
                     selectLitAlt l alts'
                   StgVarArg v ->
                     StgCase (StgApp v []) tag_bndr tagAltTy (mkDefaultLitAlt alts')
                   StgRubbishArg _ ->
                     rubbishFail

         {-
         Unit tuples. No need for an extra case expression to bind
         non-existent components. This is happening when we have something
         like

           packBool :: (# (# #) | (# #) #) -> GHC.Types.Bool
           packBool =
               \r [ds_syT] (-> GHC.Types.Bool)
                   case ds_syT of bndr {
                     (#_|#) _ [Occ=Dead] -> GHC.Types.True [];
                     (#|_#) _ [Occ=Dead] -> GHC.Types.False [];
                   };

         Here unarising bndr gives us a unit tuple, and code for the general
         case generates a redundant case expression to bind this tuple's only
         field.
         -}
         _ | Just [ty] <- unariseIdType bndr
           , UbxSumAlt _ <- alt_ty
           -> do MASSERT (ty `eqType` tagTy)
                 let bndr' = bndr `setIdType` tagTy
                 let rho' = extendVarEnv rho bndr [StgVarArg bndr']
                 alts' <- mapM (unariseSumAlt rho' []) alts
                 return (StgCase e' bndr' tagAltTy (mkDefaultLitAlt alts'))

         -- General case
         _ -> do alts' <- unariseAlts rho alt_ty bndr alts
                 let alt_ty'
                       | UbxSumAlt sum_rep <- alt_ty
                       = UbxTupAlt (length (flattenSumRep sum_rep))
                       | otherwise
                       = alt_ty
                 return (StgCase e' bndr alt_ty' alts')

unariseExpr rho (StgLet bind e)
  = StgLet <$> unariseBinding rho bind <*> unariseExpr rho e

unariseExpr rho (StgLetNoEscape bind e)
  = StgLetNoEscape <$> unariseBinding rho bind <*> unariseExpr rho e

unariseExpr rho (StgTick tick e)
  = StgTick tick <$> unariseExpr rho e

------------------------
unariseAlts :: UnariseEnv -> AltType -> Id -> [StgAlt] -> UniqSM [StgAlt]
unariseAlts rho (UbxTupAlt n) bndr [(DEFAULT, [], e)]
  = do (rho', ys) <- unariseIdBinder rho bndr
       e' <- unariseExpr rho' e
       return [(DataAlt (tupleDataCon Unboxed n), ys, e')]

unariseAlts rho (UbxTupAlt n) bndr [(DataAlt _, ys, e)]
  = do (rho', ys') <- unariseIdBinders rho ys
       let rho'' = extendVarEnv rho' bndr (map StgVarArg ys')
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

-- | Make alternatives that match on the tag of a sum.
unariseSumAlt :: UnariseEnv
              -> [StgArg] -- ^ sum components _excluding_ the tag bit.
              -> StgAlt   -- ^ original alternative with sum LHS
              -> UniqSM StgAlt
unariseSumAlt rho _ (DEFAULT, _, e)
  = ( DEFAULT, [], ) <$> unariseExpr rho e

unariseSumAlt rho args (DataAlt sumCon, bs, e)
  = do let rho' = mapSumIdBinders bs args rho
       e' <- unariseExpr rho' e
       return ( LitAlt (MachInt (fromIntegral (dataConTag sumCon))), [], e' )

unariseSumAlt _ scrt alt
  = pprPanic "unariseSumAlt" (ppr scrt $$ ppr alt)

--------------------------
unariseAlt :: UnariseEnv -> StgAlt -> UniqSM StgAlt
unariseAlt rho (con, xs, e)
  = do (rho', xs') <- unariseIdBinders rho xs
       (con, xs',) <$> unariseExpr rho' e

------------------------
unariseArg :: UnariseEnv -> StgArg -> [StgArg]
unariseArg rho (StgVarArg x) = unariseId rho x
unariseArg _   arg           = [arg]

unariseArgs :: UnariseEnv -> [StgArg] -> [StgArg]
unariseArgs rho = concatMap (unariseArg rho)

filterIdArgs :: [StgArg] -> [Id]
filterIdArgs args = [ var | StgVarArg var <- args ]

unariseId :: UnariseEnv -> Id -> [StgArg]
unariseId rho x = fromMaybe [StgVarArg x] (lookupVarEnv rho x)

unariseIds :: UnariseEnv -> [Id] -> [StgArg]
unariseIds rho = concatMap (unariseId rho)

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
unariseIdBinder rho x =
  case unariseIdType x of
    Nothing
      -> return (rho, [x])
    Just [ty]
      | ty `eqType` voidPrimTy
      -> return (extendVarEnv rho x [StgVarArg voidPrimId], [voidPrimId])
    Just tys
      -> do ys <- mkIds (mkFastString "us") tys
            return (extendVarEnv rho x (map StgVarArg ys), ys)

-- | If Id needs unarisation, return list of types of its fields.
unariseIdType :: Id -> Maybe [Type]
unariseIdType x =
  case repType (idType x) of
    UnaryRep _ -> Nothing

    UbxTupleRep tys
      | null tys  -> Just [voidPrimTy]
      | otherwise -> Just tys

    UbxSumRep sumRep -> Just (ubxSumFieldTypes sumRep)

unariseIdType' :: Id -> [Type]
unariseIdType' x = fromMaybe [idType x] (unariseIdType x)

mapTupleIdBinders
    :: [Id]      -- ^ binders of a tuple alternative
    -> [StgArg]  -- ^ arguments that form the tuple
    -> UnariseEnv
    -> UnariseEnv
mapTupleIdBinders ids args rho0
  = let
      id_arities = map (\id -> (id, length (unariseIdType' id))) ids

      map_ids :: UnariseEnv -> [(Id, Int)] -> [StgArg] -> UnariseEnv
      map_ids rho [] _  = rho
      map_ids _   _  [] = pprPanic "mapTupleIdBinders" (ppr ids $$ ppr args)
      map_ids rho ((x, x_arity) : xs) args =
        let (x_args, args') = splitAt x_arity args
         in map_ids (extendVarEnv rho x x_args) xs args'
    in
      ASSERT (sum (map snd id_arities) == length args)
      map_ids rho0 id_arities args

-- See Note [Two-step binder substitution for sums]
mapSumIdBinders
  :: [Id]        -- ^ binders of a sum alternative
  -> [StgArg]    -- ^ arguments that form the sum (NOT including the tag)
  -> UnariseEnv
  -> UnariseEnv
mapSumIdBinders ids sum_args rho
  = let
      id_us = map unariseIdType' ids

      gen_id_temps :: Int -> [(a, [b])] -> [(a, [Int])]
      gen_id_temps _ []
          = []
      gen_id_temps n ((id, l) : ls)
          = (id, [n .. n + length l - 1]) : gen_id_temps (n + length l) ls

      id_temps = gen_id_temps 0 (zip ids id_us)

      temp_tys :: [(Type, Int)]
      temp_tys = zip (concat id_us) [0..]

      scrt_arg_tys :: [(Type, StgArg)]
      scrt_arg_tys = map (\arg -> (stgArgType arg, arg)) sum_args

      -- map temporaries (temp_tys) to the StgArgs that make the sum
      -- (scrt_arg_tys)
      rns :: IM.IntMap StgArg
      rns = IM.fromList (rnUbxSumBndrs temp_tys scrt_arg_tys)

      rho' = extendVarEnvList rho $
               map (second (map (\temp -> fromJust (IM.lookup temp rns)))) id_temps
    in
      rho'

mkIds :: FastString -> [UnaryType] -> UniqSM [Id]
mkIds fs tys = mapM (mkId fs) tys

mkId :: FastString -> UnaryType -> UniqSM Id
mkId = mkSysLocalOrCoVarM

--------------------------------------------------------------------------------

tagAltTy :: AltType
tagAltTy = PrimAlt intPrimTyCon

tagTy :: Type
tagTy = intPrimTy

mkDefaultLitAlt :: [StgAlt] -> [StgAlt]
mkDefaultLitAlt [] = pprPanic "elimUbxSumExpr.mkDefaultAlt" (text "Empty alts")
mkDefaultLitAlt alts@((DEFAULT, _, _) : _) = alts
mkDefaultLitAlt ((LitAlt{}, [], rhs) : alts) = (DEFAULT, [], rhs) : alts
mkDefaultLitAlt alts = pprPanic "mkDefaultLitAlt" (text "Not a lit alt:" <+> ppr alts)

isNullaryTupleArg :: StgArg -> Bool
isNullaryTupleArg (StgVarArg v) = v == dataConWorkId unboxedUnitDataCon
isNullaryTupleArg _             = False

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
