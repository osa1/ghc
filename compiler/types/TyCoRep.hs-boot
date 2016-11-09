module TyCoRep where

import Outputable ( SDoc )

data Type
data TyThing
data Coercion
data LeftOrRight
data UnivCoProvenance
data TCvSubst

type PredType = Type
type Kind = Type
type ThetaType = [PredType]

pprKind :: Kind -> SDoc
pprType :: Type -> SDoc
