{-# LANGUAGE CPP, KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-} -- Note [Pass sensitive types]
                                      -- in module PlaceHolder
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RoleAnnotations #-}

module HsExpr where

import SrcLoc     ( Located )
import Outputable ( SDoc, Outputable )
import {-# SOURCE #-} HsPat  ( LPat )
import PlaceHolder ( OutputableBndrId )

type role HsExpr nominal
type role HsCmd nominal
type role MatchGroup nominal representational
type role GRHSs nominal representational
type role HsSplice nominal
type role SyntaxExpr nominal
data HsExpr (i :: *)
data HsCmd  (i :: *)
data HsSplice (i :: *)
data MatchGroup (a :: *) (body :: *)
data GRHSs (a :: *) (body :: *)
data SyntaxExpr (i :: *)

instance (OutputableBndrId id) => Outputable (HsExpr id)
instance (OutputableBndrId id) => Outputable (HsCmd id)

type LHsExpr a = Located (HsExpr a)

pprLExpr :: (OutputableBndrId id) => LHsExpr id -> SDoc

pprExpr :: (OutputableBndrId id) => HsExpr id -> SDoc

pprSplice :: (OutputableBndrId id) => HsSplice id -> SDoc

pprPatBind :: (OutputableBndrId bndr,
               OutputableBndrId id, Outputable body)
           => LPat bndr -> GRHSs id body -> SDoc

pprFunBind :: (OutputableBndrId idR, Outputable body)
           => MatchGroup idR body -> SDoc
