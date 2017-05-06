{-# LANGUAGE GADTs #-}

-- Not sure if this is supposed work...

data A x where
  A1 :: Int -> A Int
  A2 :: Int -> A Bool

-- This currently fails to typecheck because `A1` and `A2` have different types
f :: A x -> Int
f (A1 i | A2 i) = i

-- Same here...
g :: A x -> String
g (A1{} | A2{}) = "ok"

main = do
    print (f (A1 123))
    print (f (A2 456))
    putStrLn (g (A1 123))
    putStrLn (g (A1 456))
