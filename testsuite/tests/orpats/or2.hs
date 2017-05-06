-- top-level binding with an or pattern
([x] | (x : _ : _)) = [ 1 .. 10 ]
([y] | (y : _ : _)) = [ 2 ]

main = print x >> print y
