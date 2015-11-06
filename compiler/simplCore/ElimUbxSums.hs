{-# LANGUAGE TupleSections #-}

module ElimUbxSums ( elimUbxSums ) where

import BasicTypes
import Coercion
import CoreLint (lintPassResult)
import CoreMonad
import CoreSyn
import CoreUtils
import DataCon
import FastString (mkFastString)
import HscTypes
import Id
import IdInfo
import Literal
import MkCore
import MkId
import Outputable
import PprCore (pprCoreBindings)
import Type
import TypeRep
import TysPrim
import TysWiredIn
import UniqSupply
import Var

elimUbxSums :: ModGuts -> CoreM ModGuts
elimUbxSums guts@ModGuts{ mg_binds = binds } = do
    liftIO $ putStrLn "++++++++++++++ ELIMINATING UNBOXED SUMS ++++++++++++++"
    pprTrace "\n\nbindings before pass\n" (pprCoreBindings binds) (return ())
    binds' <- mapM elimUbxSumsBind binds
    pprTrace "\n\nbindings after pass\n" (pprCoreBindings binds') (return ())
    hscEnv <- getHscEnv
    liftIO $ lintPassResult hscEnv CoreElimUbxSums binds'
    pprTrace "lint OK" empty (return ())
    return guts{ mg_binds = binds' }

elimUbxSumsBind :: CoreBind -> CoreM CoreBind
elimUbxSumsBind (NonRec x e) =
    NonRec (elimUbxSumTy x) <$> elimUbxSumsExpr e
elimUbxSumsBind (Rec xes) =
    Rec <$> mapM (\(x, e) -> (elimUbxSumTy x,) <$> elimUbxSumsExpr e) xes

elimUbxSumsExpr :: CoreExpr -> CoreM CoreExpr
elimUbxSumsExpr (Var v) = return $ Var $ elimUbxSumTy v

elimUbxSumsExpr e@Lit{} = return e

elimUbxSumsExpr e@App{}
  | let (f, args) = collectArgs e
  , Var x     <- f
  , Just dcon <- isDataConId_maybe x
  , isUnboxedSumCon dcon
  -- , ty        <- exprType f
  -- , pprTrace "found a unboxed sum application"
  --     (text "we still need to figure out which alternative of which sum type"
  --       $+$ ppr ty
  --       $+$ (text "DataCon tag:" <+> ppr (dataConTag dcon))
  --       $+$ ppr e) False
  = case dropWhile isTypeArg args of
      [arg] -> do
        dflags <- getDynFlags
        arg'   <- elimUbxSumsExpr arg
        return $ mkConApp (tupleDataCon Unboxed 2)
                   [ -- tuple type arguments
                     Type intPrimTy, Type liftedAny,
                     -- tuple term arguments
                     Lit (mkMachInt dflags (fromIntegral (dataConTag dcon))),
                     mkUnsafeCoerce (exprType arg) liftedAny arg' ]
      _ ->
        pprPanic "unboxed sum: only one field is supported for now" (ppr e)

elimUbxSumsExpr (App e1 e2) = App <$> elimUbxSumsExpr e1 <*> elimUbxSumsExpr e2

elimUbxSumsExpr (Lam x body) = Lam (elimUbxSumTy x) <$> elimUbxSumsExpr body

elimUbxSumsExpr (Let b body) = Let <$> elimUbxSumsBind b <*> elimUbxSumsExpr body

elimUbxSumsExpr (Case scrt0 x0 ty0 alts0)
  | isUnboxedSumType (exprType scrt0)
  = do tagCaseBndr <- newUnusedId intPrimTy
       tagBinder   <- newLocalId "tag" intPrimTy
       fieldBinder <- newLocalId "field" liftedAny
       -- currently we're assuming one field only

       -- Inner pattern matching, matches the tag
       tagCase     <- Case (Var tagBinder) tagCaseBndr ty <$> mkUbxTupleAlts alts0 fieldBinder

       -- Only alt of outer case expression that matches the tuple
       let tupleAlt = (DataAlt (tupleDataCon Unboxed 2), [tagBinder, fieldBinder], tagCase)

       scrt <- elimUbxSumsExpr scrt0

       -- Outer case expression that matches the tuple
       return $ Case scrt x ty [tupleAlt]
  where
    x  = elimUbxSumTy  x0
    ty = elimUbxSumTy' ty0

    mkUbxTupleAlts :: [CoreAlt] -> Id -> CoreM [CoreAlt]

    mkUbxTupleAlts ((DEFAULT, bndrs, rhs) : rest) fieldBinder = do
      rhs' <- elimUbxSumsExpr rhs
      ((DEFAULT, map elimUbxSumTy bndrs, rhs') :) <$> mkUbxTupleAlts' rest fieldBinder

    mkUbxTupleAlts rest fieldBinder = do
      rest' <- mkUbxTupleAlts' rest fieldBinder
      let core_msg = Lit (mkMachString "") -- TODO: Runtime error message
      let def = (DEFAULT, [], mkApps (Var nON_EXHAUSTIVE_GUARDS_ERROR_ID) [Type ty, core_msg])
      return (def : rest')

    mkUbxTupleAlts' ((DataAlt con, [bndr0], rhs0) : rest) fieldBinder = do
      -- TODO: we should probably update bndr type
      dflags <- getDynFlags
      let tagLit = mkMachInt dflags (fromIntegral (dataConTag con))
      rhs <- elimUbxSumsExpr rhs0
      let bindBndr = Let (NonRec bndr0 -- TODO: Do we need to change type of this binder?
                           (mkUnsafeCoerce liftedAny (idType bndr0) (Var fieldBinder)))
      let alt      = (LitAlt tagLit, [], bindBndr rhs)
      alts <- mkUbxTupleAlts' rest fieldBinder
      return (alt : alts)

    mkUbxTupleAlts' ((altCon, _, _) : _) _ =
      pprPanic "mkUbxTupleAlts': Invalid alt con:" (ppr altCon)

    mkUbxTupleAlts' [] _ = return []

elimUbxSumsExpr (Case scrt x ty alts) = do
    scrt' <- elimUbxSumsExpr scrt
    alts' <- elimUbxSumsAlts alts
    return $ Case scrt' (elimUbxSumTy x) (elimUbxSumTy' ty) alts'

elimUbxSumsExpr (Cast e c) = Cast <$> elimUbxSumsExpr e <*> pure c

elimUbxSumsExpr (Tick t e) = Tick t <$> elimUbxSumsExpr e

elimUbxSumsExpr (Type ty) = return (Type $ elimUbxSumTy' ty)

elimUbxSumsExpr c@Coercion{} = return c

elimUbxSumsAlts :: [CoreAlt] -> CoreM [CoreAlt]
elimUbxSumsAlts = mapM elimUbxSumsAlt

elimUbxSumsAlt :: CoreAlt -> CoreM CoreAlt
elimUbxSumsAlt (con, xs, rhs) =
  -- TODO: Lint/type error is here, we need to update the DataCon(con).
  --
  -- I don't know how to solve this. I think the problem is that DataCons have
  -- bunch of types for their types etc. and we need to somehow update them.
  -- But:
  --
  -- 1. DataCons are not held in a shared symbol table etc. so we need to update
  --    them as we encounter during the pass.
  --
  -- 2. The interface gives us no way to update DataCons. (see DataCon.hs)
  --    As far as I can see, once they're built there's no way to update. We can
  --    try to read all the information and create a new DataCon. Not sure if
  --    this is possible. (some information might not be even read-only)
  --
  (con, map elimUbxSumTy xs,) <$> elimUbxSumsExpr rhs

--------------------------------------------------------------------------------
-- | Translate type of identifier
elimUbxSumTy :: Var -> Var

elimUbxSumTy v = setVarType v (elimUbxSumTy' (varType v))

elimUbxSumTy' :: Type -> Type
elimUbxSumTy' ty
  | isUnboxedSumType ty
  = mkTupleTy Unboxed [intPrimTy, liftedAny]

elimUbxSumTy' ty@TyVarTy{} = ty
elimUbxSumTy' (AppTy ty1 ty2) = AppTy (elimUbxSumTy' ty1) (elimUbxSumTy' ty2)
elimUbxSumTy' (TyConApp con args) = TyConApp con $ map elimUbxSumTy' args
elimUbxSumTy' (FunTy ty1 ty2) = FunTy (elimUbxSumTy' ty1) (elimUbxSumTy' ty2)
elimUbxSumTy' (ForAllTy v ty) = ForAllTy v $ elimUbxSumTy' ty
elimUbxSumTy' ty@LitTy{} = ty

--------------------------------------------------------------------------------

newLocalId :: String -> Type -> CoreM Id
newLocalId str ty = do
    uniq <- getUniqueM
    return (mkSysLocal (mkFastString str) uniq ty)

newUnusedId :: Type -> CoreM Id
newUnusedId ty = do
    id <- newLocalId "unused" ty
    return $ Var.lazySetIdInfo id ((idInfo id){ occInfo = IAmDead })

liftedAny :: Type
liftedAny = anyTypeOfKind liftedTypeKind

mkUnsafeCoerce :: Type -> Type -> CoreExpr -> CoreExpr
mkUnsafeCoerce from to arg = mkApps (Var unsafeCoerceId) [ Type from, Type to, arg ]
