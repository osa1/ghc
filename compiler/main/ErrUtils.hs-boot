module ErrUtils where

import Outputable (SDoc)
import SrcLoc (SrcSpan)
import {-# SOURCE #-} DynFlags (WarningFlag)

data Severity
  = SevOutput
  | SevFatal
  | SevInteractive
  | SevDump
  | SevInfo
  | SevWarning (Maybe WarningFlag)
  | SevError


type MsgDoc = SDoc

mkLocMessage :: Severity -> SrcSpan -> MsgDoc -> MsgDoc
