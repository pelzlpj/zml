external zml_print_int     : int -> unit  = "zml_print_int" in
external zml_print_newline : unit -> unit = "zml_print_newline" in

let rec fib n =
  if n <= 1 then
    1
  else
    (fib (n - 1)) + (fib (n - 2))
in
let x = fib 8 in
let y = zml_print_int x in
let z = zml_print_newline () in
()

