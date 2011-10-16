
open Printf

type file_range_t = {
(** [file_range_t] is a representation of a range of characters in a source file. *)
  fr_start : Lexing.position;   (** Starting position of a range of characters *)
  fr_end   : Lexing.position;   (** Ending position of a range of characters *)
}

type parser_meta_t = {
  range      : file_range_t;    (** Location in file where expression is found *)
  type_annot : Type.t option;   (** Type annotation for this expression, if provided *)
}

type t = {
(** Type [t] represents a node in the AST, as determined by the first pass of parsing the source file. *)
  expr        : expr_t;         (** Expression parsed at this node *)
  parser_info : parser_meta_t   (** Additional metadata recorded by the parser *)
}

and expr_t =
(** [expr_t] defines all the expressions which are supported at the syntax level. *)
  | Unit
  | Bool of bool
  | Int of int
  | Eq of t * t
  | Neq of t * t
  | Leq of t * t
  | Geq of t * t
  | Less of t * t
  | Greater of t * t
  | Add of t * t
  | Sub of t * t
  | Mul of t * t
  | Div of t * t
  | Mod of t * t
  | Not of t
  | Neg of t
  | If of t * t * t
  | Var of string
  | Let of string * (string list) * t * t     (* newly bound variable does not recur in the "equals" expression *)
  | LetRec of string * (string list) * t * t  (* newly bound variable may recur in the "equals" expression *)
  | Apply of t * (t list)


(* Construct an AST node with no type information *)
let untyped_expr expr range = {
  expr;
  parser_info = {range; type_annot = None}
}


let rec print_ast (ast : t) =
  let print_binary ident a b =
    sprintf "%s (%s, %s)" ident (print_ast a) (print_ast b)
  in
  let expr_s =
    match ast.expr with
    | Unit ->
      sprintf "()"
    | Eq (a, b) ->
      print_binary "Eq" a b
    | Neq (a, b) ->
      print_binary "Neq" a b
    | Leq (a, b) ->
      print_binary "Leq" a b
    | Geq (a, b) ->
      print_binary "Geq" a b
    | Less (a, b) ->
      print_binary "Less" a b
    | Greater (a, b) ->
      print_binary "Greater" a b
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
    | Let (a, a_list, b, c) ->
      sprintf "Let (%s, [%s], %s, %s)"
        a
        (String.concat "; " (List.fold_left (fun acc a -> acc @ [a]) [] a_list))
        (print_ast b)
        (print_ast c)
    | LetRec (a, a_list, b, c) ->
      sprintf "LetRec (%s, [%s], %s, %s)"
        a
        (String.concat "; " (List.fold_left (fun acc a -> acc @ [a]) [] a_list))
        (print_ast b)
        (print_ast c)
    | Apply (a, b_list) ->
      sprintf "Apply (%s [%s])"
        (print_ast a)
        (String.concat "; " (List.fold_left (fun acc b -> acc @ [print_ast b]) [] b_list))
  in
  let range_s =
    let print_pos pos =
      sprintf "%d:%d" pos.Lexing.pos_lnum (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
    in
    sprintf "%s-%s"
      (print_pos ast.parser_info.range.fr_start)
      (print_pos ast.parser_info.range.fr_end)
  in
  sprintf "(%s >> %s)" expr_s range_s




