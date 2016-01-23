module Type where
import {-# SOURCE #-} TyCon
import {-# SOURCE #-} TyCoRep( Type, Kind )

isPredTy :: Type -> Bool
isCoercionTy :: Type -> Bool

mkAppTy :: Type -> Type -> Type
piResultTy :: Type -> Type -> Type

isPrimitiveType :: Type -> Bool

typeKind :: Type -> Kind
eqType :: Type -> Type -> Bool

coreViewOneStarKind :: Type -> Maybe Type

partitionInvisibles :: TyCon -> (a -> Type) -> [a] -> ([a], [a])

coreView :: Type -> Maybe Type
splitTyConApp_maybe :: Type -> Maybe (TyCon, [Type])
