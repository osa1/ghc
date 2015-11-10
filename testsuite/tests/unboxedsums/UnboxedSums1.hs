{-# LANGUAGE UnboxedSums, UnboxedTuples #-}

-- Some basic tests for UnboxedSums.

module Main where

data Rec = Rec
  { sumField1 :: (# Int | Bool #)
  , sumField2 :: (# Char | String | Int #)
  }

data D = D Int (# Int | Bool #)

type Blah = (# Int | (Bool, String) #)

showBlah :: Blah -> String
showBlah x = case x of
               (# l | #) -> "Left: " ++ show l
               (# | r #) -> "Right: " ++ show r

showUbxTuple :: (Show a, Show b) => (# a | b #) -> String
showUbxTuple (# l | #) = "Left: " ++ show l
showUbxTuple (# | r #) = "Right: " ++ show r

showUbxTuple3 :: (Show a, Show b, Show c) => (# a | b | c #) -> String
showUbxTuple3 (# a1 | | #) = "Alt1: " ++ show a1
showUbxTuple3 (# | a2 | #) = "Alt2: " ++ show a2
showUbxTuple3 (# | | a3 #) = "Alt3: " ++ show a3

showRec :: Rec -> String
showRec (Rec f1 f2) =
    "Rec (" ++ showUbxTuple f1 ++ ") (" ++ showUbxTuple3 f2 ++ ")"

showD :: D -> String
showD (D i s) = "D " ++ show i ++ " (" ++ showUbxTuple s ++ ")"

main :: IO ()
main = do
  let blah1 :: Blah
      blah1 = (# 1 | #)

      blah2 :: Blah
      blah2 = (# | (False, "msg") #)

      rec1 :: Rec
      rec1 = Rec (# | True #) (# | | 123 #)

      d1 :: D
      d1 = D 10 (# 11 | #)

  putStrLn $ showBlah blah1
  putStrLn $ showBlah blah2
  putStrLn $ showRec rec1
  putStrLn $ showD d1
