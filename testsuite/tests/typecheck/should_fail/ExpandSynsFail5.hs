-- Reported by sjcjoosten in T10547, this was taking forever becuase of a bug in
-- the implementation.

module Test where

type T12 = T11
type T11 = T10
type T10 = T9
type T9  = T8
type T8  = T7
type T7  = T6
type T6  = T5
type T5  = T4
type T4  = T3
type T3  = T2
type T2  = T1
type T1  = T0
type T0  = Int

type S12 = S11
type S11 = S10
type S10 = S9
type S9  = S8
type S8  = S7
type S7  = S6
type S6  = S5
type S5  = S4
type S4  = S3
type S3  = S2
type S2  = S1
type S1  = S0
type S0  = Int

test :: (T12, Char) -> (S12, Bool) -> Int
test a b = const 1 (f a b)

f :: (a, b) -> (a, b) -> (a, b)
f a _ = a
