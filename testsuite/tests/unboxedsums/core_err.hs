{-# LANGUAGE UnboxedSums, MagicHash, UnboxedTuples #-}

module Main where

import GHC.Prim
import GHC.Types

-- This used to generate wrong Core.

showAlt0 :: (# Void# | (# #) #) -> String
showAlt0 (# | (# #) #) = "(# | (# #) #)"

main :: IO ()
main = return ()
