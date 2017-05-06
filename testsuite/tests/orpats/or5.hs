{-# LANGUAGE ViewPatterns #-}

-- is_mm in or4, but uses view patterns
is_mm' :: (Int, Int) -> Bool
is_mm' ((even -> True, _) | (_, even -> True))
  = True
is_mm' _
  = False

main = do
  print (is_mm' (2, 1)) -- True
  print (is_mm' (1, 2)) -- True, guard should be run again
