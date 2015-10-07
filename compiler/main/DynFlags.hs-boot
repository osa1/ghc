
module DynFlags where

import Platform

data DynFlags
data WarningFlag

targetPlatform       :: DynFlags -> Platform
pprUserLength        :: DynFlags -> Int
pprCols              :: DynFlags -> Int
unsafeGlobalDynFlags :: DynFlags
useUnicode     :: DynFlags -> Bool
useUnicodeSyntax     :: DynFlags -> Bool
