{-# LANGUAGE CPP #-}

module HsDoc (
  HsDocString(..),
  LHsDocString,
  ppr_mbDoc
  ) where

#include "HsVersions.h"

import Outputable
import SrcLoc
import FastString

-- | Haskell Documentation String
newtype HsDocString = HsDocString FastString
  deriving (Eq, Show)

-- | Located Haskell Documentation String
type LHsDocString = Located HsDocString

instance Outputable HsDocString where
  ppr (HsDocString fs) = ftext fs

ppr_mbDoc :: Maybe LHsDocString -> SDoc
ppr_mbDoc (Just doc) = ppr doc
ppr_mbDoc Nothing    = empty

