(******************************************************************************
 *  ZML -- an ML compiler targeting interactive fiction virtual machines
 *  Copyright (C) 2011-2012 Paul Pelzl
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License, version 2,
 *  as published by the Free Software Foundation.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 *  Please send bug reports, patches, etc. to Paul Pelzl at 
 *  <pelzlpj@gmail.com>.
 ******************************************************************************)

(* Implementation of type inference, by delegation to module AlgW. *)


module TypedNode = struct
  type 'a t = {
    expr          : 'a;
    inferred_type : Type.t;
    parser_info   : ParserMeta.parser_meta_t
  }

  type bind_t = {
    bind_name : string;
    bind_type : Type.t
  }

  let get_expr x = x.expr
  let get_parser_info x = x.parser_info
  let get_type_constraint x = x.parser_info.ParserMeta.type_annot
  let get_name binding = binding.bind_name
  let make ~expr ~inferred_type ~parser_info = { expr; inferred_type; parser_info }
  let get_type x = x.inferred_type
  let make_binding name tp = { bind_name = name; bind_type = tp }
end

module TypedLambda = AlgW.Lambda(TypedNode)
open TypedLambda
open TypedNode
type t = TypedLambda.t TypedNode.t

let rec string_of_typetree (ast : t) : string =
  let expr_s = 
    match ast.expr with
    | Unit   -> "()"
    | Bool a -> if a then "true" else "false"
    | Int a  -> string_of_int a
    | Var v  -> v
    | If (cond, true_expr, false_expr) ->
        Printf.sprintf "if %s\nthen %s\nelse %s"
          (string_of_typetree cond)
          (string_of_typetree true_expr)
          (string_of_typetree false_expr)
    | Apply (func, arg) ->
        Printf.sprintf "apply(%s, %s)"
          (string_of_typetree func) (string_of_typetree arg)
    | Lambda (binding, body) ->
        Printf.sprintf "(fun (%s : %s) -> %s)"
          binding.bind_name (Type.string_of_type binding.bind_type)
          (string_of_typetree body)
    | Let (binding, body, scope) ->
        Printf.sprintf "let (%s : %s) =\n%s in\n %s"
          binding.bind_name (Type.string_of_type binding.bind_type)
          (string_of_typetree body) (string_of_typetree scope)
    | LetRec (binding, body, scope) ->
        Printf.sprintf "let rec (%s : %s) =\n%s in\n %s"
          binding.bind_name (Type.string_of_type binding.bind_type)
          (string_of_typetree body) (string_of_typetree scope)
    | External (binding, asm_name, scope) ->
        Printf.sprintf "external %s : %s = %s in\n %s"
          binding.bind_name (Type.string_of_type binding.bind_type)
          asm_name (string_of_typetree scope)
  in
  Printf.sprintf "%s : %s" expr_s (Type.string_of_type ast.inferred_type)


let infer (parsed_expr : Syntax.t) : t =
  let module W = AlgW.Make(Syntax.UntypedNode)(TypedNode) in
  let () = TypeVar.reset_vars () in
  let _, typed_ast = W.algorithm_w AlgW.builtin_env parsed_expr in

  (* Now that typing is complete, inject External definitions for all
   * the built-in functions. *)
  List.fold_left 
    (fun ast (asm_id, ts) -> {
      expr = External (
        {bind_name = asm_id; bind_type = AlgW.instantiate ts},
        Builtins.asm_name_of_id asm_id,
        ast);
      inferred_type = ast.inferred_type;
      parser_info   = Syntax.bogus_parser_meta_t
    })
    typed_ast
    Builtins.type_env


