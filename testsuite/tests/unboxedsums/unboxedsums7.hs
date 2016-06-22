{-# LANGUAGE UnboxedSums, UnboxedTuples, MagicHash #-}

module Main where

import GHC.Prim
import GHC.Types

import System.Mem (performMajorGC)

type Either1 a b c = (# a | (# b, c #) #)

showEither1 :: (Show a, Show b, Show c) => Either1 a b c -> String
showEither1 (# left | #)  = "Left " ++ show left
showEither1 (# | (# right1, right2 #) #) = "Right " ++ show right1 ++ " " ++ show right2

main :: IO ()
main = do
    putStrLn (showEither1 e1_1)

    -- This line used to print "Right -4611686018427359531 False"
    putStrLn (showEither1 e1_2)

    -- performMajorGC

    -- putStrLn (showEither1 e1_1)
    -- putStrLn (showEither1 e1_2)
  where
    -- boxed types only
    e1_1, e1_2 :: Either1 String Int Bool
    e1_1 = (# "error" | #)
    e1_2 = (# | (# 10, True #) #)
