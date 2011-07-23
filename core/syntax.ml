
open Printf

type file_range_t = {
(** [file_range_t] is a representation of a range of characters in a source file. *)
  fr_start : Lexing.position;   (** Starting position of a range of characters *)
  fr_end   : Lexing.position;   (** Ending position of a range of characters *)
}

type type_annotation_t = {
(** [type_annotation_t] is a representation of a user-specified type annotation. *)
  ta_type  : Type.t;            (** User-specified type to assign to this expression *)
  ta_range : file_range_t;      (** Location where user specified the type information *)
}

type fun_arg_t = {
(** [fun_arg_t] is a representation of a function argument. *)
  fa_name  : string;                      (** Name of the argument *)
  fa_annot : type_annotation_t option;    (** Type annotation for the argument, if provided *)
}

type t = {
(** Type [t] represents a node in the AST, as determined by the first pass of parsing the source file. *)
  expr       : expr_t;                    (** Expression parsed at this node *)
  range      : file_range_t;              (** Location in file where expression is found *)
  type_annot : type_annotation_t option;  (** Type annotation for this expression, if provided *)
}

and expr_t =
(** [expr_t] defines all the expressions which are supported at the syntax level. *)
  | Unit
  | Eq of t * t
  | Neq of t * t
  | Leq of t * t
  | Geq of t * t
  | Less of t * t
  | Greater of t * t
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
  | LetFun of fundef_t * t    (* non-recursive function *)
  | LetRec of fundef_t * t    (* recursive function *)
and fundef_t = {
  fun_name : string;
  fun_args : fun_arg_t list;
  fun_body : t
}


(* Construct an AST node with no type information *)
let untyped_expr expr range = {
  expr = expr;
  range = range;
  type_annot = None;
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
    | Let (a, b, c) ->
      sprintf "Let (%s, %s, %s)" a (print_ast b) (print_ast c)
    | LetFun (f, a) ->
      let fun_arg_names = List.map (fun arg -> arg.fa_name) f.fun_args in
      sprintf "LetFun ((%s, %s, %s), %s)"
        f.fun_name (String.concat " " fun_arg_names) (print_ast f.fun_body) (print_ast a)
    | LetRec (f, a) ->
      let fun_arg_names = List.map (fun arg -> arg.fa_name) f.fun_args in
      sprintf "LetRec ((%s, %s, %s), %s)"
        f.fun_name (String.concat " " fun_arg_names) (print_ast f.fun_body) (print_ast a)
  in
  let range_s =
    let print_pos pos =
      sprintf "%d:%d" pos.Lexing.pos_lnum (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
    in
    sprintf "%s-%s" (print_pos ast.range.fr_start) (print_pos ast.range.fr_end)
  in
  sprintf "(%s >> %s)" expr_s range_s




