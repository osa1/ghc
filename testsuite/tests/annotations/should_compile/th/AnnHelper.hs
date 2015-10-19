module AnnHelper where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

traverseModuleAnnotations :: Q [String]
traverseModuleAnnotations = do
  ModuleInfo _currentMod children <- reifyModule =<< thisModule
  go children [] []
  where
    go []     _visited acc = return acc
    go (x:xs) visited  acc | x `elem` visited = go xs visited acc
                           | otherwise = do
                             ModuleInfo _mod newMods <- reifyModule x
                             newAnns <- reifyAnnotations $ AnnLookupModule x
                             go (newMods ++ xs) (x:visited) (newAnns ++ acc)
