module RepType where

import BasicTypes (Arity, RepArity)
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
typeRepArity :: Arity -> Type -> RepArity

instance Outputable RepType
instance Outputable UbxSumRepTy
