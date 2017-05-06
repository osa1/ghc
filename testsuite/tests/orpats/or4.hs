-- multi-match semantics test, search for "multi match" in the proposal
-- (I should probably add section numbers)

is_mm :: (Int, Int) -> Bool
is_mm ((x, _) | (_, x))
  | even x
  = True
is_mm _
  = False

main = do
  print (is_mm (2, 1)) -- True
  print (is_mm (1, 2)) -- True, guard should be run again
