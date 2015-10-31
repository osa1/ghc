{-# LANGUAGE TupleSections #-}

module ElimUbxSums ( elimUbxSums ) where

import BasicTypes
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
import MkId
import Outputable
import PprCore (pprCoreBindings)
import TyCon
import Type
import TysPrim
import TysWiredIn
import UniqSupply

import Control.Monad (when)

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
elimUbxSumsBind (NonRec x e) = NonRec x <$> elimUbxSumsExpr e
elimUbxSumsBind (Rec xes)    = Rec <$> mapM (\(x, e) -> (x,) <$> elimUbxSumsExpr e) xes

elimUbxSumsExpr :: CoreExpr -> CoreM CoreExpr
elimUbxSumsExpr e@Var{} = return e

elimUbxSumsExpr e@Lit{} = return e

elimUbxSumsExpr e@App{}
  | Var x     <- f
  , Just dcon <- isDataConId_maybe x
  , isUnboxedSumCon dcon
  , ty        <- exprType f
  -- , pprTrace "found a unboxed sum application"
  --     (text "we still need to figure out which alternative of which sum type"
  --       $+$ ppr ty
  --       $+$ (text "DataCon tag:" <+> ppr (dataConTag dcon))
  --       $+$ ppr e) False
  = case dropTyArgs args of
      [arg] -> do
        dflags <- getDynFlags
        return $ mkConApp (tupleDataCon Unboxed 2)
                   [Lit (mkMachInt dflags (fromIntegral (dataConTag dcon))),
                    App (Var unsafeCoerceId) arg]
      _ ->
        pprPanic "unboxed sum: only one field is supported for now" (ppr e)
  where
    dropTyArgs :: [CoreArg] -> [CoreArg]
    dropTyArgs [] = []
    dropTyArgs (Type _ : rest) = dropTyArgs rest
    dropTyArgs l = l

    (f, args) = collectArgs e

elimUbxSumsExpr (App e1 e2) = App <$> elimUbxSumsExpr e1 <*> elimUbxSumsExpr e2

elimUbxSumsExpr (Lam x body) = Lam x <$> elimUbxSumsExpr body

elimUbxSumsExpr (Let b body) = Let <$> elimUbxSumsBind b <*> elimUbxSumsExpr body

elimUbxSumsExpr e@(Case scrt x ty alts)
  | isUnboxedSumType (exprType scrt)
  -- , pprTrace "Found case expression" (ppr scrt $+$ ppr (expandTypeSynonyms (exprType scrt))
  --                                              $+$ ppr ty)
  = do -- let sumTyTupleTy = toTupleTy (exprType scrt)
       tagCaseBndr <- newUnusedId intPrimTy
       tagBinder   <- newLocalId "tag" intPrimTy
       fieldBinder <- newLocalId "field" anyTy
       -- currently we're assuming one field only

       -- Inner pattern matching, matches the tag
       tagCase     <- Case (Var tagBinder) tagCaseBndr ty <$> mkUbxTupleAlts alts fieldBinder

       -- Only alt of outer case expression that matches the tuple
       let tupleAlt = (DataAlt (tupleDataCon Unboxed 2), [tagBinder, fieldBinder], tagCase)

       scrt' <- elimUbxSumsExpr scrt

       -- Outer case expression that matches the tuple
       let after = Case scrt' (updateIdTy x) ty [tupleAlt]

       pprTrace "Transforming case expression"
         (ppr e $+$ text "after:" $+$ ppr after) (return after)
  where
    mkUbxTupleAlts :: [CoreAlt] -> Id -> CoreM [CoreAlt]
    -- mkUbxTupleAlts alts _
    --   | pprTrace "mkUbxTupleAlts alts" (ppr alts) False = undefined

    mkUbxTupleAlts ((DEFAULT, bndrs, rhs) : rest) fieldBinder = do
      rhs' <- elimUbxSumsExpr rhs
      ((DEFAULT, bndrs, rhs') :) <$> mkUbxTupleAlts' rest fieldBinder

    mkUbxTupleAlts rest fieldBinder = mkUbxTupleAlts' rest fieldBinder

    mkUbxTupleAlts' ((DataAlt con, [bndr], rhs) : rest) fieldBinder = do
      -- TODO: we should probably update bndr type
      dflags <- getDynFlags
      let tagLit = mkMachInt dflags (fromIntegral (dataConTag con))
      rhs' <- elimUbxSumsExpr rhs
      let bindBndr = Let (NonRec bndr $ mkApps (Var unsafeCoerceId) [ Var fieldBinder, Var bndr ])
      let alt      = (LitAlt tagLit, [], bindBndr rhs')
      alts <- mkUbxTupleAlts' rest fieldBinder
      return (alt : alts)

    mkUbxTupleAlts' [] _ = return []

    updateIdTy :: Id -> Id
    updateIdTy = id

elimUbxSumsExpr (Case scrt x ty alts) = do
    scrt' <- elimUbxSumsExpr scrt
    alts' <- elimUbxSumsAlts alts
    return $ Case scrt' x ty alts'

elimUbxSumsExpr (Cast e c) = Cast <$> elimUbxSumsExpr e <*> pure c

elimUbxSumsExpr (Tick t e) = Tick t <$> elimUbxSumsExpr e

elimUbxSumsExpr t@Type{} = return t

elimUbxSumsExpr c@Coercion{} = return c

elimUbxSumsAlts :: [CoreAlt] -> CoreM [CoreAlt]
elimUbxSumsAlts = mapM elimUbxSumsAlt

elimUbxSumsAlt :: CoreAlt -> CoreM CoreAlt
elimUbxSumsAlt (con, xs, rhs) = (con, xs,) <$> elimUbxSumsExpr rhs


newLocalId :: String -> Type -> CoreM Id
newLocalId str ty = do
    uniq <- getUniqueM
    return (mkSysLocal (mkFastString str) uniq ty)

newUnusedId :: Type -> CoreM Id
newUnusedId ty = do
    id <- newLocalId "unused" ty
    return $ lazySetIdInfo id ((idInfo id){ occInfo = IAmDead })
