module RepType where

import Outputable (Outputable)
import TyCoRep (Type)

data RepType
  = UbxTupleRep [UnaryType]
  | UbxSumRep UbxSumRepTy
  | UnaryRep UnaryType

data UbxSumRepTy
type UnaryType = Type

flattenRepType :: RepType -> [UnaryType]
repType :: Type -> RepType

instance Outputable RepType
instance Outputable UbxSumRepTy
