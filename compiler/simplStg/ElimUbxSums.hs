{-# LANGUAGE CPP, TupleSections #-}

module ElimUbxSums
  ( elimUbxSums
  , unboxedSumTyConFields
  , unboxedSumRepTypes
  ) where

#include "HsVersions.h"

import BasicTypes (Boxity (..))
import CoreSyn (AltCon (..))
import CostCentre (currentCCS)
import DataCon
import FastString (mkFastString)
import Id (idType, mkSysLocalM, setIdType)
import Literal (Literal (..))
import MkCore (rUNTIME_ERROR_ID)
import Outputable
import PrimOp (PrimOp (..), primOpSig)
import StgSyn
import TyCon
import TyCoRep (Type (..), TyBinder (..))
import Type
import TysPrim
import TysWiredIn (tupleDataCon, mkTupleTy)
import UniqSet
import UniqSet (mapUniqSet)
import UniqSupply
import Util
import VarSet (mapVarSet)

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif

import Control.Monad (replicateM)
import Data.List (partition)
import Data.Maybe (maybeToList)

--------------------------------------------------------------------------------

uBX_DUMMY_ARG, bX_DUMMY_ARG :: StgArg
uBX_DUMMY_ARG = StgLitArg (MachWord 0)
bX_DUMMY_ARG  = StgVarArg rUNTIME_ERROR_ID

--------------------------------------------------------------------------------

elimUbxSums :: [StgBinding] -> UniqSM [StgBinding]
elimUbxSums = mapM elimUbxSum

elimUbxSum :: StgBinding -> UniqSM StgBinding
elimUbxSum (StgNonRec bndr rhs)
  = StgNonRec (elimUbxSumTy bndr) <$> elimUbxSumRhs rhs (bndrType bndr)

elimUbxSum (StgRec bndrs)
  = StgRec <$> mapM (\(bndr, rhs) -> (elimUbxSumTy bndr,) <$> elimUbxSumRhs rhs (bndrType bndr)) bndrs

elimUbxSumRhs :: StgRhs -> Type -> UniqSM StgRhs
elimUbxSumRhs (StgRhsClosure ccs b_info fvs update_flag srt args expr) ty
  = StgRhsClosure ccs b_info (map elimUbxSumTy fvs)
                  update_flag (elimUbxSumSRT srt) (map elimUbxSumTy args)
      <$> elimUbxSumExpr expr (Just ty)

elimUbxSumRhs (StgRhsCon ccs con args) ty
  | isUnboxedSumCon con
  , (_, ty_args) <- splitTyConApp ty
  = do expr <- elimUbxConApp con args ty_args
       case expr of
         StgConApp con args ->
           return (StgRhsCon ccs con args)
         _ ->
           return (StgRhsClosure ccs stgSatOcc [] SingleEntry NoSRT [] expr)

  | otherwise
  = return (StgRhsCon ccs con (map elimUbxSumArg args))

elimUbxSumExpr :: StgExpr -> Maybe Type -> UniqSM StgExpr
elimUbxSumExpr (StgApp v args) _
  = return (StgApp (elimUbxSumTy v) (map elimUbxSumArg args))

elimUbxSumExpr e@StgLit{} _
  = return e

elimUbxSumExpr (StgConApp con args) ty
  | Just (tycon, ty_args) <- ty >>= splitTyConApp_maybe
  , isUnboxedSumTyCon tycon
  = do -- This can only happen in scrutinee position of case expressions.
       -- I don't like how we allow complex expressions in scrutinee position in an
       -- ANF AST. (I think this was necessary for unboxed tuples)
       elimUbxConApp con args ty_args

  | otherwise
  = return (StgConApp con (map elimUbxSumArg args))

elimUbxSumExpr (StgOpApp op args ty) _
  = return (StgOpApp op (map elimUbxSumArg args) (elimUbxSumTy' ty))

elimUbxSumExpr (StgLam args e) _
  = -- this shouldn't happen but whatever
    StgLam (map elimUbxSumTy args) <$> elimUbxSumExpr e Nothing

elimUbxSumExpr case_@(StgCase e case_lives alts_lives bndr srt alt_ty alts) ty
  | UbxSumAlt ubx_fields bx_fields <- alt_ty
  = do e' <- elimUbxSumExpr e (Just (bndrType bndr))

       let bndr' = elimUbxSumTy bndr
           srt'  = elimUbxSumSRT srt

       tag_binder <- mkSysLocalM (mkFastString "tag") intPrimTy

       -- OK, so I realized that the current implementation broken. Here's the
       -- problem: Suppose we have a nested sum, like
       --
       --   (# (# a | b #) | (# c | d #) #)
       --
       -- We translate this to
       --
       --   (# Int#, Int#, Any #)
       --
       -- Now, suppose we also have this code:
       --
       --   case (x :: our sum type) of
       --     (# a | #) ->
       --       case a of
       --         (# a | #) -> ...
       --
       -- We translate this to:
       --
       --   case x of
       --     (# tag, x1, x2 #) ->
       --       case tag of
       --         1# -> ???
       --
       -- Now, the ??? part is the tricky part. Previously the nested sum types
       -- were bound to a single variable (a), but we can't do that anymore,
       -- because we flattened the structure and now if the tag is 1, we have
       -- fields of first alt of the outer sum bound to x1 and x2, like so:
       --
       --    x1 :: Tag of the sum type in the first alt of the outer sum.
       --    x2 :: Any that stands for `a` or `b` in the first alt of the outer sum.
       --
       -- So the generated code should be something like:
       --
       --   case x of
       --     (# tag, x1, x2 #) ->
       --       case tag of
       --         1# ->
       --           case (# x1, x2 #) of
       --             (# tag1, x #) ->
       --               case tag1 of
       --                 1# -> ... x (and x2) is a ...
       --                 2# -> ... x (and x2) is b ...
       --
       -- How do we do this? We need to somehow keep track of expanded binders.
       -- i.e. we need to know that binders of outer sum fields are now expanded
       -- to multiple fields like x1 and x2. I don't know how to do this yet.

       ubx_field_binders <-
         replicateM (ubx_fields - 1) (mkSysLocalM (mkFastString "ubx") intPrimTy)

       boxed_field_binders <-
         replicateM bx_fields (mkSysLocalM (mkFastString "bx") liftedAny)

       let args = tag_binder : ubx_field_binders ++ boxed_field_binders

           mkConAlt (DataAlt con, bndrs, _useds, rhs) = do
                     -- TODO: we should probably make use of `_used`
             let
               -- mb_coerce_bndr :: Var -> Maybe PrimOp
               -- mb_coerce_bndr v =
               --   case splitTyConApp_maybe idTy of
               --     Nothing ->
               --       -- type variable - we only allow polymorphism on boxed
               --       -- types, so this has to be boxed type and so no need for a
               --       -- coercion primop. -- TODO: Where do we handle coercions
               --       -- between Any and boxed types?
               --       Nothing
               --     Just (id_tycon, [])
               --       | id_tycon == intPrimTyCon    -> Nothing
               --       | id_tycon == floatPrimTyCon  -> Just Int2FloatOp
               --       | id_tycon == doublePrimTyCon -> Just Int2DoubleOp
               --       | id_tycon == word32PrimTyCon -> Just Int2WordOp
               --       | -- Don't generate coercion for boxed types
               --         not (isPrimitiveType idTy)  -> Nothing
               --       | otherwise                   ->
               --         pprPanic "elimUbxSumExpr.mb_coerce_bndr" (ppr idTy)
               --     Just _ ->
               --       -- Pretty sure this can't be a primitive type
               --       Nothing
               --   where
               --     idTy = idType v

               rns :: [Rn]
               rns = genRns ubx_field_binders boxed_field_binders bndrs

               -- coercions :: [(Maybe PrimOp, Var)]
               -- coercions = zip (map mb_coerce_bndr bndrs) (map snd rns)

               -- apply_coercions :: [(Maybe PrimOp, Var)] -> StgExpr -> UniqSM StgExpr
               -- apply_coercions [] e                    = return e
               -- apply_coercions ((Nothing, _) : rest) e = apply_coercions rest e
               -- apply_coercions ((Just op, v) : rest) e = do
               --   e' <- apply_coercions rest e
               --   let (_, _, op_ret_ty, _, _) = primOpSig op
               --   v' <- mkSysLocalOrCoVarM (mkFastString "co") op_ret_ty
               --   let rhs :: StgRhs
               --       rhs = StgRhsClosure currentCCS stgSatOcc [v] SingleEntry NoSRT []
               --               (StgOpApp (StgPrimOp op) [StgVarArg v] op_ret_ty)
               --   return (StgLet (StgNonRec v' rhs) (rnStgExpr (v, v') e'))

             -- FIXME(osa): Disabling coercions for now.
             -- rhs_renamed <- apply_coercions coercions (foldr rnStgExpr rhs rns)
             let rhs_renamed = foldr rnStgExpr rhs rns

             -- pprTrace "mkConAlt" (text "making alt for:" <+> ppr con $$
             --                      text "bndrs:" <+> ppr bndrs $$
             --                      text "renamings:" <+> ppr rns $$
             --                      text "rhs:" <+> ppr rhs $$
             --                      text "rhs_renamed:" <+> ppr rhs_renamed) (return ())

             (LitAlt (MachInt (fromIntegral (dataConTag con))), [], [],)
               <$> elimUbxSumExpr rhs_renamed ty

           mkConAlt alt@(LitAlt{}, _, _, _) =
             pprPanic "elimUbxSumExpr.mkConAlt" (ppr alt)

           mkConAlt (DEFAULT, bndrs, useds, rhs) =
             (DEFAULT, bndrs, useds,) <$> elimUbxSumExpr rhs ty

           -- We always need a DEFAULT case, because we transform AlgAlts to
           -- PrimAlt here. Which means our pattern matching is never
           -- exhaustive, unless we had a DEFAULT case before this
           -- transformation. In that case we just use existing DEFAULT case.
           -- Otherwise we create a dummy DEFAULT case.
           mkDefaultAlt :: [StgAlt] -> [StgAlt]
           mkDefaultAlt [] = pprPanic "elimUbxSumExpr.mkDefaultAlt" (text "Empty alts")
           mkDefaultAlt alts@((DEFAULT, _, _, _) : _) = alts
           mkDefaultAlt alts = dummyDefaultAlt : alts

           dummyDefaultAlt = (DEFAULT, [], [], StgApp rUNTIME_ERROR_ID [])

       inner_case <-
         StgCase (StgApp tag_binder []) (mapUniqSet elimUbxSumTy case_lives)
                                        (mapUniqSet elimUbxSumTy alts_lives)
                                        tag_binder srt' (PrimAlt intPrimTyCon)
           . mkDefaultAlt <$> mapM mkConAlt alts

       let outer_case =
             -- TODO: not sure about lives parts
             StgCase e' (mapUniqSet elimUbxSumTy case_lives)
                        (mapUniqSet elimUbxSumTy alts_lives) bndr' srt' (UbxTupAlt (length args))
               [ (DataAlt (tupleDataCon Unboxed (length args)),
                  args,
                  replicate (length args) True, -- TODO: fix this
                  inner_case) ]

       -- pprTrace "elimubxSumExpr" (text "e:" <+> ppr e $$
       --                            text "e':" <+> ppr e' $$
       --                            text "inner_case:" <+> ppr inner_case $$
       --                            text "outer_case:" <+> ppr outer_case) $ return outer_case
       return outer_case

  | otherwise
  = do e' <- elimUbxSumExpr e (Just (bndrType bndr))
       alts' <- mapM elimUbxSumAlt alts
       return (StgCase e' (mapUniqSet elimUbxSumTy case_lives)
                          (mapUniqSet elimUbxSumTy alts_lives)
                          (elimUbxSumTy bndr) (elimUbxSumSRT srt) alt_ty alts')

elimUbxSumExpr (StgLet bind e) ty
  = StgLet <$> elimUbxSum bind <*> elimUbxSumExpr e ty

elimUbxSumExpr (StgLetNoEscape live_in_let live_in_bind bind e) ty
  = StgLetNoEscape live_in_let live_in_bind <$> elimUbxSum bind <*> elimUbxSumExpr e ty

elimUbxSumExpr (StgTick tick e) ty
  = StgTick tick <$> elimUbxSumExpr e ty

--------------------------------------------------------------------------------

genRns :: [Var] -> [Var] -> [Var] -> [Rn]
genRns _ _ [] = []
genRns ubx bx (v : vs)
  | isUnboxedSumType (bndrType v)
  = pprPanic "elimUbxSumExpr.genRns: found unboxed sum"
             (ppr v <+> parens (ppr (bndrType v)))

  | Just (tycon, args) <- splitTyConApp_maybe (bndrType v)
  , isUnboxedTupleTyCon tycon
  = -- TODO(osa): This is where we need to be careful. We need to
    -- return a [Var] instead of a single Var to handle this case.
    let
      (ubx_tys,   bx_tys)   = partition isUnLiftedType (drop (length args `div` 2) args)
      (ubx_bndrs, ubx_rest) = splitAt (length ubx_tys) ubx
      (bx_bndrs,  bx_rest)  = splitAt (length bx_tys)  bx
    in
      (v, ubx_bndrs ++ bx_bndrs) : genRns ubx_rest bx_rest vs

  | isUnLiftedType (bndrType v)
  , (ubx_v : ubx_vs) <- ubx
  = (v, [ubx_v]) : genRns ubx_vs bx vs

  | (bx_v : bx_vs) <- bx
  = (v, [bx_v]) : genRns ubx bx_vs vs

  | otherwise
  = pprPanic "elimUbxSumExpr.genRns" (ppr ubx $$ ppr bx $$ ppr (v : vs))

--------------------------------------------------------------------------------

-- | Generate and return let-bindings that apply primops to arguments + new
-- argument to apply to the DataCon. (These new arguments are bound by the let
-- bindings)
genCoercions :: [(Maybe PrimOp, StgArg)] -> UniqSM ([(Var, StgRhs)], [StgArg])
genCoercions []
  = return ([], [])

genCoercions ((Nothing, arg) : rest)
  = do (bs, as) <- genCoercions rest
       return (bs, arg : as)

genCoercions ((Just op, arg) : rest)
  = do (bs, as) <- genCoercions rest

       let
         mb_arg_var (StgVarArg v) = Just v
         mb_arg_var  StgLitArg{}  = Nothing

         (_, _, op_ret_ty, _, _) = primOpSig op

         rhs = StgRhsClosure currentCCS stgSatOcc
                             (maybeToList (mb_arg_var arg))
                             SingleEntry NoSRT []
                             (StgOpApp (StgPrimOp op) [arg] op_ret_ty)

       v <- mkSysLocalM (mkFastString "co") op_ret_ty

       return ((v, rhs) : bs, StgVarArg v : as)

mkBinding :: (Var, StgRhs) -> StgExpr -> StgExpr
mkBinding (bndr, rhs) body = StgLet (StgNonRec bndr rhs) body

--------------------------------------------------------------------------------

elimUbxSumAlt :: StgAlt -> UniqSM StgAlt
elimUbxSumAlt (con, bndrs, uses, e)
  = (con, map elimUbxSumTy bndrs, uses,) <$> elimUbxSumExpr e Nothing

--------------------------------------------------------------------------------

elimUbxSumSRT :: SRT -> SRT
elimUbxSumSRT NoSRT = NoSRT
elimUbxSumSRT (SRTEntries ids) = SRTEntries (mapVarSet elimUbxSumTy ids)

--------------------------------------------------------------------------------

elimUbxSumArg :: StgArg -> StgArg
elimUbxSumArg (StgVarArg v)
  = StgVarArg (elimUbxSumTy v)

elimUbxSumArg arg@StgLitArg{}
  = arg

elimUbxSumTy :: Var -> Var
elimUbxSumTy x = setIdType x (elimUbxSumTy' (bndrType x))

elimUbxSumTy' :: Type -> Type
elimUbxSumTy' t@TyVarTy{}
  = t

elimUbxSumTy' (AppTy t1 t2)
  = AppTy (elimUbxSumTy' t1) (elimUbxSumTy' t2)

elimUbxSumTy' (TyConApp con args)
  | isUnboxedSumTyCon con
  , (ubx_fields, bx_fields) <- unboxedSumTyConFields (drop (length args `div` 2) args)
  = mkTupleTy Unboxed (intPrimTy : replicate (ubx_fields - 1) intPrimTy ++
                                   replicate bx_fields liftedAny)

  | otherwise
  = TyConApp con (map elimUbxSumTy' args)

elimUbxSumTy' (ForAllTy (Anon t1) t2) -- FIXME:
  = ForAllTy (Anon (elimUbxSumTy' t1)) (elimUbxSumTy' t2)

elimUbxSumTy' (ForAllTy named ty)
  = ForAllTy named (elimUbxSumTy' ty)

elimUbxSumTy' ty@LitTy{}
  = ty

elimUbxSumTy' ty@CastTy{}
  = pprPanic "elimUbxSumTy'" (ppr ty)

elimUbxSumTy' ty@CoercionTy{}
  = pprPanic "elimUbxSumTy'" (ppr ty)

liftedAny :: Type
liftedAny = anyTypeOfKind liftedTypeKind

--------------------------------------------------------------------------------

-- INVARIANT: Returned list doesn't have unboxed tuples or sums.
unboxedSumRepTypes :: [Type] -> [Type]
unboxedSumRepTypes alts =
    let
      alt_tys = map go alts

      con_rep_tys_parts :: [([Type], [Type])]
      con_rep_tys_parts = map (partition isPrimitiveType) alt_tys

      fields_unboxed = maximum (0 : map (length . fst) con_rep_tys_parts)
      fields_boxed   = maximum (0 : map (length . snd) con_rep_tys_parts)

      go ty
        | Just (tc, args) <- splitTyConApp_maybe ty
        , isUnboxedTupleTyCon tc
        = drop (length args `div` 2) args

        | Just (tc, args) <- splitTyConApp_maybe ty
        , isUnboxedSumTyCon tc
        = unboxedSumRepTypes (drop (length args `div` 2) args)

        | otherwise
        = [ty]

      ret = intPrimTy :
            replicate fields_unboxed intPrimTy ++
            replicate fields_boxed liftedAny
    in
      ASSERT (not (any isUnboxedSumType ret) && not (any isUnboxedTupleType ret))
      -- pprTrace "unboxedSumRetTypes"
      --   (text "input:" <+> ppr alts $$
      --    text "con_rep_tys_parts:" <+> ppr con_rep_tys_parts $$
      --    text "output:" <+> ppr ret) $
        ret

-- | Returns (# unboxed fields, # boxed fields) for a UnboxedSum TyCon
-- application. NOTE: Tag field is included.
unboxedSumTyConFields :: [Type] -> (Int, Int)
unboxedSumTyConFields alts =
    let
      rep_tys = unboxedSumRepTypes alts
      (ubx_tys, bx_tys) = partition isPrimitiveType rep_tys
    in
      (length ubx_tys, length bx_tys)

elimUbxConApp :: DataCon -> [StgArg] -> [Type] -> UniqSM StgExpr
elimUbxConApp con stg_args ty_args0
  = ASSERT (isUnboxedSumCon con)
    -- One assumption here is that we only have one argument. The reason is
    -- because alts of sum types accept only one argument and multiple arguments
    -- are handled using unboxed tuples.
    ASSERT (length stg_args == 1)
    -- pprTrace "elimUbxConApp"
    --   (text "con:" <+> ppr con $$
    --    text "stg_args:" <+> ppr stg_args $$
    --    text "ty_args:" <+> ppr ty_args) $
    let
      ty_args = drop (length ty_args0 `div` 2) ty_args0

      [arg0] = stg_args
      arg_ty = elimUbxSumTy' (stgArgType arg0)
      arg = elimUbxSumArg arg0

      (fields_unboxed, fields_boxed) = unboxedSumTyConFields ty_args

      tuple_con = tupleDataCon Unboxed (fields_unboxed + fields_boxed)

      tag_arg   = StgLitArg (MachWord (fromIntegral (dataConTag con)))

      stgArgVar (StgVarArg v) = v
      stgArgVar  StgLitArg{} = error "stgArgVar"
    in
      case () of
        _ | Just (tycon, args0) <- splitTyConApp_maybe arg_ty
          , isUnboxedTupleTyCon tycon
          -> do -- pprTrace "found nested unboxed tuple"
                  -- (text "args:" <+> ppr args $$
                  --  text "fields_unboxed:" <+> ppr fields_unboxed $$
                  --  text "fields_boxed:" <+> ppr fields_boxed) (return ())
                let args = map elimUbxSumTy' (drop (length args0 `div` 2) args0)
                tupleBndrs <- mapM (mkSysLocalM (mkFastString "tup")) args

                let (ubx_bndrs, bx_bndrs) = partition (isPrimitiveType . idType) tupleBndrs

                    arg_var = stgArgVar arg
                    con_args =
                      tag_arg :
                      map StgVarArg ubx_bndrs ++
                        replicate (fields_unboxed - length ubx_bndrs - 1) uBX_DUMMY_ARG ++
                      map StgVarArg bx_bndrs ++
                        replicate (fields_boxed - length bx_bndrs) bX_DUMMY_ARG

                    case_ = StgCase (StgApp arg_var [])
                                    (unitUniqSet arg_var)
                                    (mkUniqSet tupleBndrs)
                                    arg_var
                                    NoSRT
                                    (UbxTupAlt (length tupleBndrs))
                                    [ (DataAlt (head (tyConDataCons tycon)),
                                       tupleBndrs,
                                       replicate (length tupleBndrs) True,
                                       StgConApp tuple_con con_args) ]

                -- pprTrace "elimUbxConApp" (text "case:" <+> ppr case_ $$
                --                           text "con:" <+> ppr con $$
                --                           text "stg_args:" <+> ppr stg_args $$
                --                           text "ty_args0:" <+> ppr ty_args0 $$
                --                           text "ty_args:" <+> ppr ty_args $$
                --                           text "tupleBndrs:" <+> ppr tupleBndrs $$
                --                           text "con_args:" <+> ppr con_args $$
                --                           text "arg_var:" <+> ppr arg_var $$
                --                           text "arg_var type:" <+> ppr (idType arg_var)) $
                return case_

          | isPrimitiveType arg_ty
          -> let args =
                   tag_arg : arg :
                   replicate (fields_unboxed - 1) uBX_DUMMY_ARG ++
                   replicate fields_boxed bX_DUMMY_ARG
              in return (StgConApp tuple_con args)

          | otherwise
          -> let args =
                   tag_arg :
                   replicate (fields_unboxed - 1) uBX_DUMMY_ARG ++
                   [arg] ++
                   replicate (fields_boxed - 1) bX_DUMMY_ARG
              in return (StgConApp tuple_con args)

--------------------------------------------------------------------------------

bndrType :: Var -> Type
bndrType = expandTypeSynonyms . idType

--------------------------------------------------------------------------------
-- * Variable renaming
--
-- NOTE: This is not a substitution! We sometimes replace a single variable with
-- multiple variables, by replacing the variable with an application of an
-- unboxed tuple constructor. Similarly if the variable is at an argument
-- position, we end up applying more arguments by replacing one variable with
-- many variables!
--
-- TODO: Give this a different name to avoid confusion with variable
-- substitution.

type Rn = (Var, [Var])

-- Do I need to worry about capturing and shadowing here? I think every binder
-- in the program has a unique 'Unique'.

rnStgExpr :: Rn -> StgExpr -> StgExpr
rnStgExpr r (StgApp f [])
  = case rnStgVar r f of
      [f'] -> StgApp f' []
      vs   -> StgConApp (tupleDataCon Unboxed (length vs)) (map StgVarArg vs)

rnStgExpr r@(v, vs) e@(StgApp f as)
  | v == f && length vs > 1
  = pprPanic "rnStgExpr: can't replace variable at function position"
      (text "rn:" <+> ppr r $$
       text "expr:" <+>  ppr e)

  | [f'] <- rnStgVar r f
  = StgApp f' (rnStgArgs r as)

  | otherwise
  = pprPanic "rnStgExpr: bug happened" (ppr r $$ ppr e)

rnStgExpr _ e@StgLit{}
  = e

rnStgExpr rn (StgConApp con as)
  = StgConApp con (rnStgArgs rn as)

rnStgExpr rn (StgOpApp op args ty)
  = StgOpApp op (rnStgArgs rn args) ty

rnStgExpr rn (StgLam args body)
  = StgLam args (rnStgExpr rn body)

rnStgExpr rn (StgCase scrt case_lives alts_lives bndr srt altty alts)
  = StgCase (rnStgExpr rn scrt) (rnLives rn case_lives) (rnLives rn alts_lives)
            bndr (rnSRT rn srt) altty (rnStgAlts rn alts)

rnStgExpr rn (StgLet bind body)
  = StgLet (rnStgBinding rn bind) (rnStgExpr rn body)

rnStgExpr rn (StgLetNoEscape live_in_let live_in_bind bind e)
  = StgLetNoEscape (rnLives rn live_in_let) (rnLives rn live_in_bind) bind
                   (rnStgExpr rn e)

rnStgExpr rn (StgTick t e)
  = StgTick t (rnStgExpr rn e)

rnStgBinding :: Rn -> StgBinding -> StgBinding
rnStgBinding rn (StgNonRec bndr rhs)
  = StgNonRec bndr (rnStgRhs rn rhs)

rnStgBinding rn (StgRec bs)
  = StgRec (map (\(bndr, rhs) -> (bndr, rnStgRhs rn rhs)) bs)

rnStgRhs :: Rn -> StgRhs -> StgRhs
rnStgRhs rn (StgRhsClosure ccs b_info fvs update_flag srt args expr)
  = StgRhsClosure ccs b_info (concatMap (rnStgVar rn) fvs) update_flag
                  (rnSRT rn srt) args (rnStgExpr rn expr)

rnStgRhs rn (StgRhsCon ccs con args)
  = StgRhsCon ccs con (rnStgArgs rn args)

rnStgArgs :: Rn -> [StgArg] -> [StgArg]
rnStgArgs = concatMap . rnStgArg

rnStgArg :: Rn -> StgArg -> [StgArg]
rnStgArg rn (StgVarArg v)
  = map StgVarArg (rnStgVar rn v)
rnStgArg _ a@StgLitArg{} = [a]

rnStgAlts :: Rn -> [StgAlt] -> [StgAlt]
rnStgAlts = map . rnStgAlt

rnStgAlt :: Rn -> StgAlt -> StgAlt
rnStgAlt rn (pat, bndrs, uses, rhs)
  = (pat, concatMap (rnStgVar rn) bndrs, uses, rnStgExpr rn rhs)

rnLives :: Rn -> StgLiveVars -> StgLiveVars
rnLives rn us = mkUniqSet (concatMap (rnStgVar rn) (uniqSetToList us))

rnSRT :: Rn -> SRT -> SRT
rnSRT _ NoSRT = NoSRT
rnSRT rn (SRTEntries s) = SRTEntries (mkUniqSet (concatMap (rnStgVar rn) (uniqSetToList s)))

rnStgVar :: Rn -> Var -> [Var]
rnStgVar (v1, v2) v3
  | v1 == v3  = v2
  | otherwise = [v3]
