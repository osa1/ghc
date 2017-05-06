data T = T1 String | T2 String | T3 Int

stringOfT :: T -> Maybe String

stringOfT (T1 s | T2 s) = Just s

-- overlaps and wildcards with different types are OK
stringOfT (T2 _ | T3 _) = Nothing

main = do
  print (stringOfT (T1 "foo"))
  print (stringOfT (T2 "bar"))
  print (stringOfT (T3 123))
