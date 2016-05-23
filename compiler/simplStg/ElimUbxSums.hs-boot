module ElimUbxSums where

import {-# SOURCE #-} TyCoRep (Type)
import {-# SOURCE #-} Type (RepType)
import Outputable (Outputable)

data UbxSumRepTy
instance Outputable UbxSumRepTy
ubxSumRepType :: [Type] -> RepType
flattenSumRep :: UbxSumRepTy -> [Type]
