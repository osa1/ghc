{-
(c) The GRASP/AQUA Project, Glasgow University, 1992-2012


Note [Unarisation]
~~~~~~~~~~~~~~~~~~

The idea of this pass is to translate away *all* unboxed-tuple binders. So for example:

f (x :: (# Int, Bool #)) = f x + f (# 1, True #)
 ==>
f (x1 :: Int) (x2 :: Bool) = f x1 x2 + f 1 True

It is important that we do this at the STG level and NOT at the core level
because it would be very hard to make this pass Core-type-preserving.

STG fed to the code generators *must* be unarised because the code generators do
not support unboxed tuple binders natively.


Note [Unarisation and arity]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Because of unarisation, the arity that will be recorded in the generated info table
for an Id may be larger than the idArity. Instead we record what we call the RepArity,
which is the Arity taking into account any expanded arguments, and corresponds to
the number of (possibly-void) *registers* arguments will arrive in.
-}

{-# LANGUAGE CPP #-}

module UnariseStg (unarise) where

#include "HsVersions.h"

import BasicTypes
import CoreSyn
import DataCon
import FastString (FastString, mkFastString)
import Id
import Literal (Literal (..))
import MkCore (rUNTIME_ERROR_ID)
import MkId (realWorldPrimId)
import Name
import OccName
import Outputable
import StgSyn
import TyCon
import Type
import TysPrim (intPrimTy, anyTypeOfKind, intPrimTyCon)
import TysWiredIn
import UniqSupply
import Util
import VarEnv
import VarSet

import Data.Bifunctor (second)
import Data.List (partition)
import Data.Maybe (fromMaybe)

import ElimUbxSums

-- | A mapping from unboxed-tuple binders to the Ids they were expanded to.
--
-- INVARIANT: Ids in the range don't have unboxed tuple types.
--
-- Those in-scope variables without unboxed-tuple types are not present in
-- the domain of the mapping at all.
type UnariseEnv = VarEnv [Id]

ubxTupleId0 :: Id
ubxTupleId0 = dataConWorkId (tupleDataCon Unboxed 0)

unarise :: UniqSupply -> [StgBinding] -> [StgBinding]
unarise us binds = zipWith (\us -> unariseBinding us init_env) (listSplitUniqSupply us) binds
  where -- See Note [Nullary unboxed tuple] in Type.hs
        init_env = unitVarEnv ubxTupleId0 [realWorldPrimId]

unariseBinding :: UniqSupply -> UnariseEnv -> StgBinding -> StgBinding
unariseBinding us rho bind = case bind of
  StgNonRec x rhs -> StgNonRec x (unariseRhs us rho rhs (idType x))
  StgRec xrhss    -> StgRec $ zipWith (\us (x, rhs) -> (x, unariseRhs us rho rhs (idType x)))
                                      (listSplitUniqSupply us) xrhss

unariseRhs :: UniqSupply -> UnariseEnv -> StgRhs -> Type -> StgRhs
unariseRhs us rho rhs ty = case rhs of
  StgRhsClosure ccs b_info fvs update_flag srt args expr
    -> StgRhsClosure ccs b_info (unariseIds rho fvs) update_flag
                     (unariseSRT rho srt) args'
                     (unariseExpr us' rho' expr (dropFunArgs (length args) ty))
    where (us', rho', args') = unariseIdBinders us rho args
  StgRhsCon ccs con args
    -> StgRhsCon ccs con (unariseArgs rho args)

------------------------
unariseExpr :: UniqSupply -> UnariseEnv -> StgExpr -> Type -> StgExpr
unariseExpr _ rho (StgApp f args) ty
  | null args
  , UbxTupleRep tys <- repType (idType f)
  =  -- Particularly important where (##) is concerned
     -- See Note [Nullary unboxed tuple]
    StgConApp (tupleDataCon Unboxed (length tys))
              (map StgVarArg (unariseId rho f))

  | null args
  , Just (tycon, ty_args) <- splitTyConApp_maybe ty
  , isUnboxedSumTyCon tycon
  , (ubx_fields, bx_fields) <- unboxedSumTyConFields (dropLevityArgs ty_args)
  , (ubx_args, bx_args) <- partition (isUnLiftedType . idType) (unariseId rho f)
  = StgConApp (tupleDataCon Unboxed (ubx_fields + bx_fields))
              (map StgVarArg ubx_args ++
               replicate (ubx_fields - length ubx_args) uBX_DUMMY_ARG ++
               map StgVarArg bx_args ++
               replicate (bx_fields - length bx_args) bX_DUMMY_ARG)

  -- We now use rho for renaming too
  | Just [f'] <- lookupVarEnv rho f
  = StgApp f' (unariseArgs rho args)

  | otherwise
  = StgApp f (unariseArgs rho args)

unariseExpr _ _ (StgLit l) _
  = StgLit l

unariseExpr _ rho e@(StgConApp dc args) ty
  | isUnboxedTupleCon dc
  = StgConApp (tupleDataCon Unboxed (length args')) args'

  | isUnboxedSumCon dc
  , (tycon, ty_args) <- splitTyConApp ty
  , (ubx_fields, bx_fields) <- unboxedSumTyConFields (dropLevityArgs ty_args)
  , (ubx_args, bx_args) <- partition (isUnLiftedType . stgArgType) args'
  , let tag = dataConTag dc
  = StgConApp (tupleDataCon Unboxed (ubx_fields + bx_fields))
              (mkTagArg tag :
               ubx_args ++ replicate (ubx_fields - length ubx_args - 1) uBX_DUMMY_ARG ++
               bx_args ++ replicate (bx_fields - length bx_args) bX_DUMMY_ARG)

  | otherwise
  = StgConApp dc args'
  where
    args' = unariseArgs rho args

unariseExpr _ rho (StgOpApp op args ty) _
  = StgOpApp op (unariseArgs rho args) ty

unariseExpr _ _ e@StgLam{} _
  = pprPanic "unariseExpr: found lambda" (ppr e)

unariseExpr us rho case_@(StgCase e case_lives alts_lives bndr srt alt_ty alts) ty
  = let ret = StgCase (unariseExpr us1 rho e (idType bndr))
                      (unariseLives rho case_lives) (unariseLives rho alts_lives)
                      bndr (unariseSRT rho srt) alt_ty' alts'
     in -- pprTrace "unariseExpr" (text "before:" <+> ppr case_ $$
        --                         text "after:" <+> ppr ret $$
        --                         text "type:" <+> ppr ty)
        ret
 where
    (us1, us2) = splitUniqSupply us
    alts'      = unariseAlts us2 rho alt_ty bndr alts ty
    alt_ty'    = case alt_ty of
                   UbxSumAlt ubx_fields bx_fields -> UbxTupAlt (ubx_fields + bx_fields)
                   _ -> alt_ty

unariseExpr us rho (StgLet bind e) ty
  = StgLet (unariseBinding us1 rho bind) (unariseExpr us2 rho e ty)
  where
    (us1, us2) = splitUniqSupply us

unariseExpr us rho (StgLetNoEscape live_in_let live_in_bind bind e) ty
  = StgLetNoEscape (unariseLives rho live_in_let) (unariseLives rho live_in_bind)
                   (unariseBinding us1 rho bind) (unariseExpr us2 rho e ty)
  where
    (us1, us2) = splitUniqSupply us

unariseExpr us rho (StgTick tick e) ty
  = StgTick tick (unariseExpr us rho e ty)

------------------------
unariseAlts :: UniqSupply -> UnariseEnv -> AltType -> Id -> [StgAlt] -> Type -> [StgAlt]
unariseAlts us rho (UbxTupAlt n) bndr [(DEFAULT, [], [], e)] ty
  = [(DataAlt (tupleDataCon Unboxed n), ys, uses, unariseExpr us2' rho' e ty)]
  where
    (us2', rho', ys) = unariseIdBinder us rho bndr
    uses = replicate (length ys) (not (isDeadBinder bndr))

unariseAlts us rho (UbxTupAlt n) bndr [(DataAlt _, ys, uses, e)] ty
  = [(DataAlt (tupleDataCon Unboxed n), ys', uses', unariseExpr us2' rho'' e ty)]
  where
    (us2', rho', ys', uses') = unariseUsedIdBinders us rho ys uses
    rho'' = extendVarEnv rho' bndr ys'

unariseAlts _ _ (UbxTupAlt _) _ alts _
  = pprPanic "unariseExpr: strange unboxed tuple alts" (ppr alts)

unariseAlts us rho (UbxSumAlt ubx_fields bx_fields) bndr alts ty
  = ASSERT (length ys == ubx_fields + bx_fields)
    [(DataAlt (tupleDataCon Unboxed (ubx_fields + bx_fields)), ys, uses, inner_case)]
  where
    (us2, rho_sum_bndrs, ys) = unariseIdBinder us rho bndr
    uses = replicate (length ys) (not (isDeadBinder bndr))
    (tag_bndr : ubx_ys, bx_ys) = splitAt ubx_fields ys

    inner_case =
      let
        mkAlt :: StgAlt -> StgAlt
        mkAlt (DataAlt sumCon, bs, uses, e) =
          let
            (us', rho_alt_bndrs, bs') = unariseIdBinders us rho_sum_bndrs bs
            (ubx_bs, bx_bs) = partition (isUnLiftedType . idType) bs'
            rns = zip ubx_bs ubx_ys ++ zip bx_bs bx_ys

            rho_alt_bndrs_renamed =
              flip mapVarEnv rho_alt_bndrs $ \vals ->
                map (\val -> fromMaybe val (lookup val rns)) vals

            rho_alt_bndrs_orig_bndr_added =
              extendVarEnvList rho_alt_bndrs_renamed (map (second (:[])) rns)

            ret = unariseExpr us2 rho_alt_bndrs_orig_bndr_added e ty
          in
            --pprTrace "mkAlt" (text "unarising alt with rns:" <+> ppr rho''' $$
            --                  text "rho'':" <+> ppr rho'' $$
            --                  text "rho':" <+> ppr rho' $$
            --                  text "rho:" <+> ppr rho $$
            --                  text "rns:" <+> ppr rns $$
            --                  ppr e $$ ppr ty $$ text "ret:" <+> ppr ret) -- (text "alt bs:" $$ ppr bs $$ ppr ubx_bs $$ ppr bx_bs $$ ppr rns)
            ( LitAlt (MachInt (fromIntegral (dataConTag sumCon))), [], [],
              ret )

        mkAlt (DEFAULT, _, _, e) =
          ( DEFAULT, [], [], unariseExpr us2 rho_sum_bndrs e ty )
      in
        StgCase (StgApp tag_bndr []) undefined undefined tag_bndr undefined
                (PrimAlt intPrimTyCon)
                (mkDefaultAlt (map mkAlt alts))

unariseAlts us rho _ _ alts ty
  = zipWith (\us alt -> unariseAlt us rho alt ty) (listSplitUniqSupply us) alts

--------------------------
unariseAlt :: UniqSupply -> UnariseEnv -> StgAlt -> Type -> StgAlt
unariseAlt us rho (con, xs, uses, e) ty
  = (con, xs', uses', unariseExpr us' rho' e ty)
  where
    (us', rho', xs', uses') = unariseUsedIdBinders us rho xs uses

------------------------
unariseSRT :: UnariseEnv -> SRT -> SRT
unariseSRT _   NoSRT            = NoSRT
unariseSRT rho (SRTEntries ids) = SRTEntries (concatMapVarSet (unariseId rho) ids)

unariseLives :: UnariseEnv -> StgLiveVars -> StgLiveVars
unariseLives rho ids = concatMapVarSet (unariseId rho) ids

unariseArgs :: UnariseEnv -> [StgArg] -> [StgArg]
unariseArgs rho = concatMap (unariseArg rho)

unariseArg :: UnariseEnv -> StgArg -> [StgArg]
unariseArg rho (StgVarArg x) = map StgVarArg (unariseId rho x)
unariseArg _   (StgLitArg l) = [StgLitArg l]

unariseIds :: UnariseEnv -> [Id] -> [Id]
unariseIds rho = concatMap (unariseId rho)

unariseId :: UnariseEnv -> Id -> [Id]
unariseId rho x
  | Just ys <- lookupVarEnv rho x
  = -- Disabling the assertion as we also use the env for renaming now.
    -- ASSERT2( case repType (idType x) of UbxTupleRep{} -> True; UbxSumRep{} -> True; _ -> x == ubxTupleId0
    --        , text "unariseId: not unboxed tuple or sum" <+> ppr x <+> parens (ppr (idType x)) )
    ys

  | otherwise
  = -- ASSERT2( case repType (idType x) of UbxTupleRep{} -> False; UbxSumRep{} -> False; _ -> True
    --        , text "unariseId: was unboxed tuple or sum" <+> ppr x )
    [x]

unariseUsedIdBinders :: UniqSupply -> UnariseEnv -> [Id] -> [Bool]
                     -> (UniqSupply, UnariseEnv, [Id], [Bool])
unariseUsedIdBinders us rho xs uses
  = case mapAccumL2 do_one us rho (zipEqual "unariseUsedIdBinders" xs uses) of
      (us', rho', xs_usess) -> uncurry ((,,,) us' rho') (unzip (concat xs_usess))
  where
    do_one us rho (x, use) = third3 (map (flip (,) use)) (unariseIdBinder us rho x)

unariseIdBinders :: UniqSupply -> UnariseEnv -> [Id] -> (UniqSupply, UnariseEnv, [Id])
unariseIdBinders us rho xs = third3 concat $ mapAccumL2 unariseIdBinder us rho xs

unariseIdBinder :: UniqSupply -> UnariseEnv -> Id -> (UniqSupply, UnariseEnv, [Id])
unariseIdBinder us rho x = case repType (idType x) of
    UnaryRep _      -> (us, rho, [x])
    UbxTupleRep tys ->
      let
        (us0, us1) = splitUniqSupply us
        ys   = -- unboxedTupleBindersFrom us0 x tys
               mkIds us0 (mkFastString "tup") tys
        rho' = extendVarEnv rho x ys
      in
        (us1, rho', ys)
    UbxSumRep ubx_fields bx_fields ->
      let
        (us0, us1) = splitUniqSupply us
        (us0_1, us0_2) = splitUniqSupply us0
        ys = -- unboxedTupleBindersFrom us0 x
             mkIds us0_1 (mkFastString "ubx") (replicate (length ubx_fields) intPrimTy) ++
             mkIds us0_2 (mkFastString "bx")  (replicate (length bx_fields) liftedAny)
        rho' = extendVarEnv rho x ys
      in
        (us1, rho', ys)

-- unboxedTupleBindersFrom :: UniqSupply -> Id -> [UnaryType] -> [Id]
-- unboxedTupleBindersFrom us x tys = mkIds us fs tys
--   where fs = occNameFS (getOccName x)

mkIds :: UniqSupply -> FastString -> [UnaryType] -> [Id]
mkIds us fs tys = zipWith (mkSysLocalOrCoVar fs) (uniqsFromSupply us) tys

concatMapVarSet :: (Var -> [Var]) -> VarSet -> VarSet
concatMapVarSet f xs = mkVarSet [x' | x <- varSetElems xs, x' <- f x]

--------------------------------------------------------------------------------

liftedAny :: Type
liftedAny = anyTypeOfKind liftedTypeKind

uBX_DUMMY_ARG :: StgArg
uBX_DUMMY_ARG = StgLitArg (MachWord 0)

bX_DUMMY_ARG :: StgArg
bX_DUMMY_ARG = StgVarArg rUNTIME_ERROR_ID

mkDefaultAlt :: [StgAlt] -> [StgAlt]
mkDefaultAlt [] = pprPanic "elimUbxSumExpr.mkDefaultAlt" (text "Empty alts")
mkDefaultAlt alts@((DEFAULT, _, _, _) : _) = alts
-- mkDefaultAlt ((LitAlt{}, [], [], rhs) : alts) = (DEFAULT, [], [], rhs) : alts
mkDefaultAlt alts = dummyDefaultAlt : alts

dummyDefaultAlt :: StgAlt
dummyDefaultAlt = (DEFAULT, [], [], StgApp rUNTIME_ERROR_ID [])

dropFunArgs :: Int -> Type -> Type
dropFunArgs n ty =
    let (bs, ty') = splitPiTys ty in mkForAllTys (drop n bs) ty'

mkTagArg :: Int -> StgArg
mkTagArg = StgLitArg . MachInt . fromIntegral
