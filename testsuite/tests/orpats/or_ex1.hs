{-# LANGUAGE ExistentialQuantification #-}

data Show'
  = forall x . Show x => Show1 x
  | forall x . Show x => Show2 x

{-# NOINLINE s #-}
s :: Show' -> String
s (Show1 x | Show2 x) = show x

main = do
    putStrLn (s (Show1 123))
    putStrLn (s (Show2 True))
