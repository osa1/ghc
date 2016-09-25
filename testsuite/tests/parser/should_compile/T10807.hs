{-# LANGUAGE MultiWayIf #-}

module T10807 where

-- This is how we had to use multi-way if previously. Not indenting lines after
-- `|` was causing a parse error.
f1 x = if | even x
           , x /= 0
           -> True
          | otherwise
           -> False

-- Non-indenting lines after `|` was working when brackets were used.
f2 x = if { | even x
            , x /= 0
            -> True
          ; | otherwise
            -> False
          };

-- This was previously causing a parse error, but actually it should work.
f3 x = if | even x
          , x /= 0
          -> True
          | otherwise
          -> False
