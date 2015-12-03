{-# LANGUAGE UnboxedSums, MagicHash #-}

-- FIXME: We're getting a type error without this:
{-# LANGUAGE UnboxedTuples #-}

module Main where

import GHC.Prim
import GHC.Types

type Either1 a b = (# a | b #)

showEither1 :: (Show a, Show b) => Either1 a b -> String
showEither1 (# left | #)  = "Left " ++ show left
showEither1 (# | right #) = "Right " ++ show right

showEither2 :: (# Int# | Float# #) -> String
showEither2 (# i | #) = "Left " ++ show (I# i)
showEither2 (# | f #) = "Right " ++ show (F# f)

showEither3 :: Show a => (# a | Int# #) -> String
showEither3 (# a | #) = "Left " ++ show a
showEither3 (# | i #) = "Right " ++ show (I# i)

-- FIXME: This is causing a panic:
--
-- ghc-stage1: panic! (the 'impossible' happened)
--   (GHC version 7.11.20151203 for x86_64-unknown-linux):
--         ASSERT failed! file compiler/codeGen/StgCmmUtils.hs, line 398
--
-- showEither4
--   :: (# Int | Bool | String | Char | Either Int Bool | Int# | Float# #)
--   -> String
-- showEither4 (# i | | | | | | #) = "Alt0: " ++ show i
-- showEither4 (# | b | | | | | #) = "Alt1: " ++ show b
-- showEither4 (# | | s | | | | #) = "Alt2: " ++ show s
-- showEither4 (# | | | c | | | #) = "Alt3: " ++ show c
-- showEither4 (# | | | | e | | #) = "Alt4: " ++ show e
-- showEither4 (# | | | | | i | #) = "Alt5: " ++ show (I# i)
-- showEither4 (# | | | | | | f #) = "Alt6: " ++ show (F# f)

main :: IO ()
main = do
    putStrLn (showEither1 e1_1)
    putStrLn (showEither1 e1_2)
    putStrLn (showEither2 e2_1)
    putStrLn (showEither2 e2_2)
    putStrLn (showEither3 e3_1)
    putStrLn (showEither3 e3_2)
    -- putStrLn (showEither4 e4_1)
    -- putStrLn (showEither4 e4_2)
    -- putStrLn (showEither4 e4_3)
  where
    -- boxed types only
    e1_1, e1_2 :: Either1 String Int
    e1_1 = (# "error" | #)
    e1_2 = (# | 10 #)

    -- prim types only
    e2_1, e2_2 :: (# Int# | Float# #)
    e2_1 = (# 10# | #)
    e2_2 = (# | 1.2# #)

    -- a mix of prim and boxed types
    e3_1, e3_2 :: (# String | Int# #)
    e3_1 = (# "OK" | #)
    e3_2 = (# | 123# #)

    -- big arity
    -- e4_1, e4_2, e4_3
    --   :: (# Int | Bool | String |
    --         Char | Either Int Bool | Int# | Float# #)
    -- e4_1 = (# 10 | | | | | | #)
    -- e4_2 = (# | | | | | 123# | #)
    -- e4_3 = (# | | | | Right True | | #)
