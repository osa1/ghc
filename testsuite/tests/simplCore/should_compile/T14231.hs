-- -fstatic-argument-transformation used to generate ill-typed Core for this
-- program

module T14231 where

bindWith :: (a -> a) -> a -> a
bindWith k f = k (bindWith k f)
