-- Synonyms shouldn't be expanded since type error is visible without
-- expansions

module Main where

type T a = [a]

f :: T Int -> String
f = undefined

main = putStrLn $ f (undefined :: T Bool)
