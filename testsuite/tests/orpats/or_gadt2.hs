{-# LANGUAGE GADTs #-}

data B x where
  B1 :: Int  -> B Int
  B2 :: Bool -> B Int

f :: B x -> String
f (B1 _ | B2 _) = "ok"

main = do
    putStrLn (f (B1 123))
    putStrLn (f (B2 True))
