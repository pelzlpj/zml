external zml_print_dec : int -> unit = "zml_print_dec" in
(** [zml_print_dec a] prints integer [a] using decimal notation. *)

external zml_print_newline : unit -> unit = "zml_print_newline" in
(** [zml_print_newline ()] prints a newline character. *)

external zml_exit : unit -> unit = "zml_exit" in
(** [zml_exit ()] causes the program to terminate immediately. *)


(*
let f x = x in
let g = f in
let z = g 6 in
*)

let make_fun x =
  let f y = x + y in
  f
in
let g = make_fun 5 in
let h = g in
let i = if true then g else h in
let z = h 6 in
()

