{-# LANGUAGE MultiWayIf #-}

module T10807 where

-- This is how we had to use multi-way if previously. Not indenting lines after
-- `|` was causing a parse error.
f1 x = if | even x
           , x /= 0
           -> True
          | otherwise
           -> False

-- This was previously causing a parse error, but actually it should work.
f2 x = if | even x
          , x /= 0
          -> True
          | otherwise
          -> False

-- If we don't generate {} in MultiWayIf we get a shift/reduce conflict here:
-- The last guard can be a part of the "if" or the "case". The correct parse
-- depends on the indentation. In we choose to reduce, then we get an "if" with
-- one condition only, which is again an error.
--
-- If we shift, we get a non-exhaustive pattern error when argument is odd.
-- If we reduce, we run the unreachable code when argument is odd.
f3 x = case x of
         x' | even x'   -> if | even x' -> 1 | otherwise -> error "should be unreachable"
            | otherwise -> 3

main :: IO ()
main = print (f3 1)
