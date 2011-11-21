let rec fib n =
  if n <= 0 then
    1
  else
    n + (fib (n - 1))
in
let x = fib 5 in
()

