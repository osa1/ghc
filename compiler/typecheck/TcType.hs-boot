module TcType where
import Outputable( SDoc )
import {-# SOURCE #-} TypeRep

data MetaDetails

data TcTyVarDetails
pprTcTyVarDetails :: TcTyVarDetails -> SDoc

pickyEqType :: Type -> Type -> Bool
