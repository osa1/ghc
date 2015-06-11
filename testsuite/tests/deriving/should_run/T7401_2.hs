{-# LANGUAGE EmptyDataDecls #-}

data Foo deriving (Show, Read, Eq, Ord)

main = print $ (undefined :: Foo) `compare` (undefined :: Foo)
