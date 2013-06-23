
open Printf
open ParserMeta


module UntypedNode = struct
  type 'a t = {
  (** Type [t] represents a node in the AST, as determined by the first pass of parsing the source file. *)
    expr        : 'a;             (** Expression parsed at this node *)
    parser_info : parser_meta_t   (** Additional metadata recorded by the parser *)
  }

  type bind_t = string

  let get_expr x = x.expr
  let get_parser_info x = x.parser_info
  let get_type_constraint x = x.parser_info.type_annot
  let get_name binding = binding
  let make ~expr ~parser_info = { expr; parser_info }
end

module UntypedLambda = AlgW.Lambda(UntypedNode)
open UntypedLambda
open UntypedNode
type t = UntypedLambda.t UntypedNode.t


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

(* In a couple of places we need to make up a parser_meta_t which doesn't actually get
 * used anywhere. *)
let bogus_parser_meta_t = {
  range = {fr_start = Lexing.dummy_pos; fr_end = Lexing.dummy_pos};
  type_annot = None
}

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
    | External (a, b, c) ->
      sprintf "External (%s, %s, %s)" a b (print_ast c)
    | Apply (f, arg) ->
      sprintf "Apply (%s %s)" (print_ast f) (print_ast arg)
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




