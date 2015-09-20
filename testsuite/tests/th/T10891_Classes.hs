{-# LANGUAGE TypeFamilies #-}

module T10891_Classes where

class C a where
  f :: a -> Int

class C' a where
  type F a :: *
  type F a = a
  f' :: a -> Int

class C'' a where
  data Fd a :: *

instance C' Int where
  type F Int = Bool
  f' = id

instance C'' Int where
  data Fd Int = B Bool | C Char
