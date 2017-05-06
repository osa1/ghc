{-# LANGUAGE GADTs #-}

data C where
  C1 :: Show a => a -> C
  C2 :: Show a => a -> C

f :: C -> String
f (C1 a | C2 a) = show a

main = do
  putStrLn (f (C1 123))
  putStrLn (f (C2 True))
