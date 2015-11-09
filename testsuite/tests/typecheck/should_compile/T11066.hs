{-# LANGUAGE GADTs #-}

module T11066 where

data Foo a where
  Foo1 :: Foo Char
  Foo2 :: Foo Int

data TyEquality a b where
  Refl :: TyEquality a a

checkTEQ :: Foo t -> Foo u -> Maybe (TyEquality t u)
checkTEQ x y = error "unimportant"

-- Problem: Operationally, step1 and step2 should be the same. But previously
-- the type checker was rejecting step2 and accepting step1. See also #11066.

step1 :: Bool
step1 =
 let foo d =
       case checkTEQ Foo1 d of
         Just Refl -> True
         Nothing -> False
 in foo Foo2

step2 :: Bool
step2 = case checkTEQ Foo1 Foo2 of
          Just Refl -> True -- Previously an "inaccessible code" error.
          Nothing -> False
