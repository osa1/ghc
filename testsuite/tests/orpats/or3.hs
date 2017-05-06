-- should print a list of `True`s
main = print
  [ ((\ (x | x) -> x) 0) == 0
  , ((\ ([x] | (x : _ : _)) -> x) [1, 2, 3]) == 1
  , (\ (Left x | Right x) -> x) (Left 1) == 1
  , (\ (Left x | Right x) -> x) (Right 1) == 1
  , (\ ((x, _) | (_, x)) -> x) (1, 2) == 1
  , (\ (([x] | [x, _]) | ([x, _, _] | [x, _, _, _])) -> x) [1, undefined, undefined, undefined] == 1
  , (\ (1 | 2 | 3) -> True) 3 == True
  , ((\ ~(Left x | Right x) -> 0 :: Int) undefined) == 0
  ]
