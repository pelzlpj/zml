
open Printf

(* Elements of the untyped AST *)
type t = 
  | Unit
  | Eq of t * t
  | Less of t * t
  | Not of t
  | Bool of bool
  | Int of int
  | Var of string
  | Neg of t
  | Add of t * t
  | Sub of t * t
  | Mul of t * t
  | Div of t * t
  | Mod of t * t
  | If of t * t * t
  | Let of string * t * t
  | LetRec of fundef_t * t
and fundef_t = {
  fun_name : string;
  fun_args : string list;
  fun_body : t
}


let rec print_ast ast =
  let print_binary ident a b =
    sprintf "%s (%s, %s)" ident (print_ast a) (print_ast b)
  in
  match ast with
  | Unit ->
    sprintf "()"
  | Eq (a, b) ->
    print_binary "Eq" a b
  | Less (a, b) ->
    print_binary "Less" a b
  | Not a ->
    sprintf "Not (%s)" (print_ast a)
  | Bool a ->
    if a then sprintf "true" else sprintf "false"
  | Int a ->
    sprintf "%d" a
  | Var a ->
    sprintf "%s" a
  | Neg a ->
    sprintf "Neg (%s)" (print_ast a)
  | Add (a, b) ->
    print_binary "Add" a b
  | Sub (a, b) ->
    print_binary "Sub" a b
  | Mul (a, b) ->
    print_binary "Mul" a b
  | Div (a, b) ->
    print_binary "Div" a b
  | Mod (a, b) ->
    print_binary "Mod" a b
  | If (a, b, c) ->
    sprintf "If (%s, %s, %s)" (print_ast a) (print_ast b) (print_ast c)
  | Let (a, b, c) ->
    sprintf "Let (%s, %s, %s)" a (print_ast b) (print_ast c)
  | LetRec (f, a) ->
    sprintf "LetRec ((%s, %s, %s), %s)"
      f.fun_name (String.concat " " f.fun_args) (print_ast f.fun_body) (print_ast a)



