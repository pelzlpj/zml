external zml_print_dec : int -> unit = "zml_print_dec" in
(** [zml_print_dec a] prints integer [a] using decimal notation. *)

external zml_print_newline : unit -> unit = "zml_print_newline" in
(** [zml_print_newline ()] prints a newline character. *)

external zml_exit : unit -> unit = "zml_exit" in
(** [zml_exit ()] causes the program to terminate immediately. *)


let a = 1 in
let f x = a + x in
let y = zml_print_dec (f 2) in
let z = zml_print_newline () in
()

