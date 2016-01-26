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
import Type
import TysPrim (intPrimTy, anyTypeOfKind, intPrimTyCon)
import TysWiredIn
import DataCon
import OccName
import Name
import UniqSupply
import Util
import VarEnv
import VarSet

import Data.Bifunctor (second)
import Data.List (partition)

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
  StgNonRec x rhs -> StgNonRec x (unariseRhs us rho rhs)
  StgRec xrhss    -> StgRec $ zipWith (\us (x, rhs) -> (x, unariseRhs us rho rhs))
                                      (listSplitUniqSupply us) xrhss

unariseRhs :: UniqSupply -> UnariseEnv -> StgRhs -> StgRhs
unariseRhs us rho rhs = case rhs of
  StgRhsClosure ccs b_info fvs update_flag args expr
    -> StgRhsClosure ccs b_info (unariseIds rho fvs) update_flag
                     args' (unariseExpr us' rho' expr)
    where (us', rho', args') = unariseIdBinders us rho args
  StgRhsCon ccs con args
    -> StgRhsCon ccs con (unariseArgs rho args)

------------------------
unariseExpr :: UniqSupply -> UnariseEnv -> StgExpr -> StgExpr
unariseExpr _ rho (StgApp f args)
  | null args
  , UbxTupleRep tys <- repType (idType f)
  =  -- Particularly important where (##) is concerned
     -- See Note [Nullary unboxed tuple]
    StgConApp (tupleDataCon Unboxed (length tys))
              (map StgVarArg (unariseId rho f))

  | null args
  , ty <- idType f
  , UbxSumRep ubx_fields bx_fields <- repType ty
  , (ubx_args, bx_args) <- partition (isUnLiftedType . idType) (unariseId rho f)
  = -- This is simple, we have the type information so we just fill blanks with
    -- dummy variables.
    -- TODO: Actually, I'm not sure if we have type information here. Id type
    -- may not be precise enough?
    -- pprTrace "unariseExpr" (text "sum var type:" <+> ppr ty) $
    StgConApp (tupleDataCon Unboxed (length ubx_fields + length bx_fields))
              (map StgVarArg ubx_args ++
               replicate (length ubx_fields - length ubx_args) uBX_DUMMY_ARG ++
               map StgVarArg bx_args ++
               replicate (length bx_fields - length bx_args) bX_DUMMY_ARG)

  | otherwise
  = StgApp f (unariseArgs rho args)

unariseExpr _ _ (StgLit l)
  = StgLit l

unariseExpr _ rho e@(StgConApp dc args)
  | isUnboxedTupleCon dc = StgConApp (tupleDataCon Unboxed (length args')) args'
  | isUnboxedSumCon dc   =
    -- TODO: This is where we need the type information, because we need to pass
    -- some number of dummy unlifted and lifted things to the constructor.
    -- (so yeah type also tells us which constructor to use)
    pprPanic "unariseExpr" (text "found sum con app:" <+> ppr e)
  | otherwise            = StgConApp dc args'
  where
    args' = unariseArgs rho args

unariseExpr _ rho (StgOpApp op args ty)
  = StgOpApp op (unariseArgs rho args) ty

unariseExpr us rho (StgLam xs e)
  = StgLam xs' (unariseExpr us' rho' e)
  where
    (us', rho', xs') = unariseIdBinders us rho xs

unariseExpr us rho case_@(StgCase e bndr alt_ty alts)
  = let ret = StgCase (unariseExpr us1 rho e) bndr alt_ty' alts'
     in pprTrace "unariseExpr" (text "before:" <+> ppr case_ $$ text "after:" <+> ppr ret) ret
 where
    (us1, us2) = splitUniqSupply us
    alts'      = unariseAlts us2 rho alt_ty bndr alts
    alt_ty'    = case alt_ty of
                   UbxSumAlt ubx_fields bx_fields -> UbxTupAlt (ubx_fields + bx_fields)
                   _ -> alt_ty

unariseExpr us rho (StgLet bind e)
  = StgLet (unariseBinding us1 rho bind) (unariseExpr us2 rho e)
  where
    (us1, us2) = splitUniqSupply us

unariseExpr us rho (StgLetNoEscape bind e)
  = StgLetNoEscape (unariseBinding us1 rho bind) (unariseExpr us2 rho e)
  where
    (us1, us2) = splitUniqSupply us

unariseExpr us rho (StgTick tick e)
  = StgTick tick (unariseExpr us rho e)

------------------------
unariseAlts :: UniqSupply -> UnariseEnv -> AltType -> Id -> [StgAlt] -> [StgAlt]
unariseAlts us rho (UbxTupAlt n) bndr [(DEFAULT, [], [], e)]
  = [(DataAlt (tupleDataCon Unboxed n), ys, uses, unariseExpr us2' rho' e)]
  where
    (us2', rho', ys) = unariseIdBinder us rho bndr
    uses = replicate (length ys) (not (isDeadBinder bndr))

unariseAlts us rho (UbxTupAlt n) bndr [(DataAlt _, ys, uses, e)]
  = [(DataAlt (tupleDataCon Unboxed n), ys', uses', unariseExpr us2' rho'' e)]
  where
    (us2', rho', ys', uses') = unariseUsedIdBinders us rho ys uses
    rho'' = extendVarEnv rho' bndr ys'

unariseAlts _ _ (UbxTupAlt _) _ alts
  = pprPanic "unariseExpr: strange unboxed tuple alts" (ppr alts)

unariseAlts us rho (UbxSumAlt ubx_fields bx_fields) bndr alts
  = ASSERT (length ys == ubx_fields + bx_fields)
    [(DataAlt (tupleDataCon Unboxed (ubx_fields + bx_fields)), ys, undefined, inner_case)]
  where
    (us2, rho', ys) = unariseIdBinder us rho bndr
    (tag_bndr : ubx_ys, bx_ys) = partition (isUnLiftedType . idType) ys

    inner_case =
      let
        mkAlt :: StgAlt -> StgAlt
        mkAlt (DataAlt sumCon, bs, uses, e) =
          let
            (ubx_bs, bx_bs) = partition (isUnLiftedType . idType) bs
            rns = map (second (:[])) (zip ubx_bs ubx_ys ++ zip bx_bs bx_ys)
            rho'' = extendVarEnvList rho' rns
          in
            ( LitAlt (MachInt (fromIntegral (dataConTag sumCon))), [], [],
              unariseExpr us2 rho'' e )
      in
        StgCase (StgApp tag_bndr []) undefined undefined tag_bndr undefined
                (PrimAlt intPrimTyCon)
                (mkDefaultAlt (map mkAlt alts))

    -- (us', rho', ys', uses') = unariseUsedIdBinders us rho ys uses
    -- (ubx_ys, bx_ys) = partition (isUnLiftedType . idType) ys'

    -- unused_ubxs = zipWith (mkSysLocalOrCoVar (mkFastString "ubx"))
    --                       (uniqsFromSupply us'1)
    --                       (replicate (ubx_fields - length ubx_ys) intPrimTy)

    -- unused_bxs = zipWith (mkSysLocalOrCoVar (mkFastString "bx"))
    --                      (uniqsFromSupply us'2)
    --                      (replicate (bx_fields - length bx_ys) liftedAny)

unariseAlts us rho _ _ alts
  = zipWith (\us alt -> unariseAlt us rho alt) (listSplitUniqSupply us) alts

--------------------------
unariseAlt :: UniqSupply -> UnariseEnv -> StgAlt -> StgAlt
unariseAlt us rho (con, xs, uses, e)
  = (con, xs', uses', unariseExpr us' rho' e)
  where
    (us', rho', xs', uses') = unariseUsedIdBinders us rho xs uses

------------------------
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
  = ASSERT2( case repType (idType x) of UbxTupleRep{} -> False; UbxSumRep{} -> False; _ -> True
           , text "unariseId: was unboxed tuple or sum" <+> ppr x )
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
    UbxTupleRep tys -> let (us0, us1) = splitUniqSupply us
                           ys   = unboxedTupleBindersFrom us0 x tys
                           rho' = extendVarEnv rho x ys
                       in (us1, rho', ys)
    UbxSumRep ubx_fields bx_fields
                    -> let (us0, us1) = splitUniqSupply us
                           ys = unboxedTupleBindersFrom us0 x
                                   (replicate (length ubx_fields) intPrimTy ++
                                    replicate (length bx_fields) liftedAny)
                           rho' = extendVarEnv rho x ys
                        in (us1, rho', ys)

unboxedTupleBindersFrom :: UniqSupply -> Id -> [UnaryType] -> [Id]
unboxedTupleBindersFrom us x tys = mkIds us fs tys
  where fs = occNameFS (getOccName x)

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
mkDefaultAlt alts = dummyDefaultAlt : alts

dummyDefaultAlt = (DEFAULT, [], [], StgApp rUNTIME_ERROR_ID [])
