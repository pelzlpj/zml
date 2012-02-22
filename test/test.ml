external zml_print_dec : int -> unit = "zml_print_dec" in
(** [zml_print_dec a] prints integer [a] using decimal notation. *)

external zml_print_newline : unit -> unit = "zml_print_newline" in
(** [zml_print_newline ()] prints a newline character. *)

external zml_exit : unit -> unit = "zml_exit" in
(** [zml_exit ()] causes the program to terminate immediately. *)


let rec fib n =
  if n <= 1 then
    1
  else
    (fib (n - 1)) + (fib (n - 2))
in
let x = fib 8 in
let y = zml_print_dec in
let z = y x in
let z = zml_print_newline () in
let f x y = x + y in
(*let g = f x in*)
()

