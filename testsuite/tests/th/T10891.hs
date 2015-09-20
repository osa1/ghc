module Main where

import T10891_Classes

import Language.Haskell.TH

main :: IO ()
main = do
  putStrLn $(stringE . show =<< reify ''C)
  putStrLn $(stringE . show =<< reify ''C')
  putStrLn $(stringE . show =<< reify ''C'')
