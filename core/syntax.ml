
open Printf

type file_range_t = {
(** [file_range_t] is a representation of a range of characters in a source file. *)
  fr_start : Lexing.position;   (** Starting position of a range of characters *)
  fr_end   : Lexing.position;   (** Ending position of a range of characters *)
}

type parser_meta_t = {
  range      : file_range_t;                (** Location in file where expression is found *)
  type_annot : Type.type_scheme_t option;   (** Type annotation for this expression, if provided *)
}

type builtin_func_t =
  | Eq
  | Neq
  | Leq
  | Geq
  | Less
  | Greater
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Not
  | Neg
(*  | ArrayMake *)
  | ArrayGet
  | ArraySet


type t = {
(** Type [t] represents a node in the AST, as determined by the first pass of parsing the source file. *)
  expr        : expr_t;         (** Expression parsed at this node *)
  parser_info : parser_meta_t   (** Additional metadata recorded by the parser *)
}

and func_t =
  | BuiltinFunc of builtin_func_t
  | FuncExpr of t

and expr_t =
(** [expr_t] defines all the expressions which are supported at the syntax level. *)
  | Unit
  | Bool of bool
  | Int of int
  | If of t * t * t
  | Var of string
  | Let of string * t * t                       (* newly bound variable does not recur in the body *)
  | LetRec of string * t * t                    (* newly bound variable may recur in the body *)
  | Lambda of string * t                        (* unary lambda definition *)
  | External of string * Type.type_scheme_t *
                string * t                      (* external (assembly passthrough) function declaration *)
  | Apply of func_t * t                         (* application of a function to a single argument *)


(* Construct an AST node with no type information *)
let untyped_expr expr range = {
  expr;
  parser_info = {range; type_annot = None}
}

(* Construct an AST node with type information *)
let typed_expr expr type_annot range = {
  expr;
  parser_info = {range; type_annot = Some type_annot}
}

let print_builtin a = 
  match a with
  | Eq          -> "Eq"
  | Neq         -> "Neq"
  | Leq         -> "Leq"
  | Geq         -> "Geq"
  | Less        -> "Less"
  | Greater     -> "Greater"
  | Add         -> "Add"
  | Sub         -> "Sub"
  | Mul         -> "Mul"
  | Div         -> "Div"
  | Mod         -> "Mod"
  | Not         -> "Not"
  | Neg         -> "Neg"
(*  | ArrayMake   -> "ArrayMake" *)
  | ArrayGet    -> "ArrayGet"
  | ArraySet    -> "ArraySet"


let rec print_ast (ast : t) =
  let expr_s =
    match ast.expr with
    | Unit ->
      sprintf "()"
    | Bool a ->
      if a then sprintf "true" else sprintf "false"
    | Int a ->
      sprintf "%d" a
    | Var a ->
      sprintf "%s" a
    | If (a, b, c) ->
      sprintf "If (%s, %s, %s)" (print_ast a) (print_ast b) (print_ast c)
    | Let (a, b, c) ->
      sprintf "Let (%s, %s, %s)"
        a
        (print_ast b)
        (print_ast c)
    | LetRec (a, b, c) ->
      sprintf "LetRec (%s, %s, %s)"
        a
        (print_ast b)
        (print_ast c)
    | Lambda (a, b) ->
      sprintf "Lambda (%s, %s)" a (print_ast b)
    | External (a, a_typ, b, c) ->
      sprintf "External (%s, %s, %s)" a b (print_ast c)
    | Apply (f, arg) ->
      let func_str =
        match f with
        | BuiltinFunc a -> print_builtin a
        | FuncExpr    a -> print_ast a
      in
      sprintf "Apply (%s %s)" func_str (print_ast arg)
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




