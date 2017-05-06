{-# LANGUAGE BangPatterns #-}

import Control.Exception

succ1, fail1, succ2, fail2 :: Monad m => m ()

succ1 = do
  let (Left x | Right x) = undefined
  return ()

fail1 = do
  let !(Left x | Right x) = undefined
  return ()

-- does not fail
succ2 = do
  let e@(Left !x | Right x) = Right undefined
  e `seq` return ()

-- fails
fail2 = do
  let e@(Left !x | Right x) = Left undefined
  e `seq` return ()

try' :: IO () -> IO (Either ErrorCall ())
try' = try

main = do
    try' succ1 >>= print
    try' fail1 >>= print
    try' succ2 >>= print
    try' fail2 >>= print
