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


(* Implementation of type inference, roughly following Algorithm W of
 * Damas and Milner. *)


open Typing_unify

exception Unbound_value of string * Syntax.parser_meta_t

exception Duplicate_argument_inner of string
exception Duplicate_argument of string * Syntax.parser_meta_t


module SMap = Map.Make(String)
module SSet = Set.Make(String)


(* Exceptionless variant of Map.find. *)
let smap_find x m =
  try Some (SMap.find x m)
  with Not_found -> None


type expr_t =
  | Unit                                                 (* Unit literal *)
  | Bool of bool                                         (* Boolean literal *)
  | Int of int                                           (* Integer literal *)
  | Eq of aexpr_t * aexpr_t                              (* Polymorphic equality *)
  | Neq of aexpr_t * aexpr_t                             (* Polymorphic inequality *)
  | Leq of aexpr_t * aexpr_t                             (* Polymorphic "less than or equal to" *)
  | Geq of aexpr_t * aexpr_t                             (* Polymorphic "greater than or equal to" *)
  | Less of aexpr_t * aexpr_t                            (* Polymorphic "less than" *)
  | Greater of aexpr_t * aexpr_t                         (* Polymorphic "greater than" *)
  | Add of aexpr_t * aexpr_t                             (* Integer addition *)
  | Sub of aexpr_t * aexpr_t                             (* Integer subtraction *)
  | Mul of aexpr_t * aexpr_t                             (* Integer multiplication *)
  | Div of aexpr_t * aexpr_t                             (* Integer division *)
  | Mod of aexpr_t * aexpr_t                             (* Integer modulus *)
  | Not of aexpr_t                                       (* Boolean negation *)
  | Neg of aexpr_t                                       (* Integer negation *)
  | If of aexpr_t * aexpr_t * aexpr_t                    (* Conditional expression *)
  | Var of string                                        (* Bound variable *)
  | Let of bind_t * (bind_t list) * aexpr_t * aexpr_t    (* Let expression *)
  | LetRec of bind_t * (bind_t list) * aexpr_t * aexpr_t (* Let Rec expression *)
  | External of bind_t * string * aexpr_t                (* External function definition *)
  | Apply of aexpr_t * (aexpr_t list)                    (* Function application *)

and aexpr_t = {
  expr          : expr_t;                (* Expression *)
  inferred_type : Type.t;                (* Inferred type of expression (possibly a typevar) *)
  parser_info   : Syntax.parser_meta_t   (* Additional info from parser regarding this expr *)
}

and bind_t = {
  bind_name : string;
  bind_type : Type.t
}


(* Recursively annotate all subexpressions with types.
 *    env         : environment in which the expression is evaluated; maps bindings to types
 *    parsed_expr : an untyped expression, as obtained from the parser
 *)
let rec annotate (env : Type.t SMap.t) (parsed_expr : Syntax.t) : aexpr_t =
  let parser_info = parsed_expr.Syntax.parser_info in
  match parsed_expr.Syntax.expr with
  | Syntax.Unit ->
      {expr = Unit; inferred_type = Type.Unit; parser_info}
  | Syntax.Bool a ->
      {expr = Bool a; inferred_type = Type.Bool; parser_info}
  | Syntax.Int a ->
      {expr = Int a; inferred_type = Type.Int; parser_info}
  | Syntax.Eq (a, b) ->
      {expr = Eq (annotate env a, annotate env b); inferred_type = Type.Bool; parser_info}
  | Syntax.Neq (a, b) ->
      {expr = Neq (annotate env a, annotate env b); inferred_type = Type.Bool; parser_info}
  | Syntax.Leq (a, b) ->
      {expr = Leq (annotate env a, annotate env b); inferred_type = Type.Bool; parser_info}
  | Syntax.Geq (a, b) ->
      {expr = Geq (annotate env a, annotate env b); inferred_type = Type.Bool; parser_info}
  | Syntax.Less (a, b) ->
      {expr = Less (annotate env a, annotate env b); inferred_type = Type.Bool; parser_info}
  | Syntax.Greater (a, b) ->
      {expr = Greater (annotate env a, annotate env b); inferred_type = Type.Bool; parser_info}
  | Syntax.Add (a, b) ->
      {expr = Add (annotate env a, annotate env b); inferred_type = Type.Int; parser_info}
  | Syntax.Sub (a, b) ->
      {expr = Sub (annotate env a, annotate env b); inferred_type = Type.Int; parser_info}
  | Syntax.Mul (a, b) ->
      {expr = Mul (annotate env a, annotate env b); inferred_type = Type.Int; parser_info}
  | Syntax.Div (a, b) ->
      {expr = Div (annotate env a, annotate env b); inferred_type = Type.Int; parser_info}
  | Syntax.Mod (a, b) ->
      {expr = Mod (annotate env a, annotate env b); inferred_type = Type.Int; parser_info}
  | Syntax.Not a ->
      {expr = Not (annotate env a); inferred_type = Type.Bool; parser_info}
  | Syntax.Neg a ->
      {expr = Neg (annotate env a); inferred_type = Type.Int; parser_info}
  | Syntax.If (a, b, c) -> {
      expr          = If (annotate env a, annotate env b, annotate env c);
      inferred_type = Type.make_type_var ();
      parser_info
    }
  | Syntax.Var var_name ->
      let var_type = match smap_find var_name env with
        | Some known_type -> known_type
        | None            -> raise (Unbound_value (var_name, parser_info))
      in {
        expr          = Var var_name;
        inferred_type = var_type;
        parser_info
      }
  | Syntax.Let (a, args, b, c) ->
      begin try {
        expr          = annotate_let false env a args b c;
        inferred_type = Type.make_type_var ();
        parser_info
      } with Duplicate_argument_inner arg_name ->
        raise (Duplicate_argument (arg_name, parser_info))
      end
  | Syntax.LetRec (a, args, b, c) ->
      begin try {
        expr = annotate_let true env a args b c;
        inferred_type = Type.make_type_var ();
        parser_info
      } with Duplicate_argument_inner arg_name ->
        raise (Duplicate_argument (arg_name, parser_info))
      end
  | Syntax.External (a_name, a_type, a_impl, b) -> 
      let env = SMap.add a_name a_type env in {
      expr = External ({bind_name = a_name; bind_type = a_type}, a_impl, annotate env b);
      inferred_type = Type.make_type_var ();
      parser_info
    }
  | Syntax.Apply (a, args) -> {
      expr          = Apply (annotate env a, List.map (annotate env) args);
      inferred_type = Type.make_type_var ();
      parser_info
    }


(* Annotate a let-binding with type variables. *) 
and annotate_let is_rec env binding args eq_expr in_expr =
  (* The first element in the list is the newly-bound variable, which is added to
   * the environment of the "in" clause (shadowing any previous binding). *)
  let fun_binding = {bind_name = binding; bind_type = Type.make_type_var () } in
  let in_env = SMap.add fun_binding.bind_name fun_binding.bind_type env in
  (* If this is a "let rec" form, then the binding may recur in the "equals"
   * clause, so the binding must be added to the eq_env. *)
  let env = if is_rec then in_env else env in
  (* All other elements in the list are function arguments, which are added to the
   * environment of the "equals" clause (shadowing any previous binding).  But
   * first we run a quick check for duplicate argument names... *)
  let _ = List.fold_left
    (fun acc arg_name ->
      if SSet.mem arg_name acc then
        raise (Duplicate_argument_inner arg_name)
      else
        SSet.add arg_name acc)
    SSet.empty
    args
  in
  let arg_bindings = List.map
    (fun arg_name -> {bind_name = arg_name; bind_type = Type.make_type_var ()})
    args
  in
  let eq_env = List.fold_left
    (fun env_acc arg_binding -> SMap.add arg_binding.bind_name arg_binding.bind_type env_acc)
    env
    arg_bindings
  in 
  if is_rec then
    LetRec (fun_binding, arg_bindings, annotate eq_env eq_expr, annotate in_env in_expr)
  else
    Let    (fun_binding, arg_bindings, annotate eq_env eq_expr, annotate in_env in_expr)



(* Given a list of type-annotated expressions, generate the list of type
 * constraints which are imposed by the expression structure. *)
let rec compute_constraints (acc : constraint_t list) (aexprs : aexpr_t list) : constraint_t list =
  match aexprs with
  | [] ->
      acc
  | {expr = Unit; _} :: tail
  | {expr = Bool _; _} :: tail
  | {expr = Int _ ; _} :: tail
  | {expr = Var _; _} :: tail ->
      compute_constraints acc tail
  | {expr = Eq  (a, b); _} :: tail
  | {expr = Neq (a, b); _} :: tail ->
      (* Polymorphic comparisons; lhs and rhs must have the same type *)
      let constr = {
        left_type  = a.inferred_type;
        right_type = b.inferred_type;
        error_info = a.parser_info
      } in
      compute_constraints (constr :: acc) (a :: b :: tail)
  | {expr = Leq (a, b); _}     :: tail
  | {expr = Geq (a, b); _}     :: tail
  | {expr = Less (a, b); _}    :: tail
  | {expr = Greater (a, b); _} :: tail ->
      (* Comparisons on ordered types; at present, arguments must be integers *)
      let a_constr = {
        left_type  = a.inferred_type;
        right_type = Type.Int;
        error_info = a.parser_info
      } in
      let b_constr = {
        left_type  = b.inferred_type;
        right_type = Type.Int;
        error_info = b.parser_info
      } in
      compute_constraints (a_constr :: b_constr :: acc) (a :: b :: tail)
  | {expr = Add (a, b); _} :: tail
  | {expr = Sub (a, b); _} :: tail
  | {expr = Mul (a, b); _} :: tail
  | {expr = Div (a, b); _} :: tail
  | {expr = Mod (a, b); _} :: tail ->
      (* Binary integer operations *)
      let a_constr = {
        left_type  = a.inferred_type;
        right_type = Type.Int;
        error_info = a.parser_info
      } in
      let b_constr = {
        left_type  = b.inferred_type;
        right_type = Type.Int;
        error_info = b.parser_info
      } in
      compute_constraints (a_constr :: b_constr :: acc) (a :: b :: tail)
  | {expr = Not a; _} :: tail ->
      (* Unitary boolean operation *)
      let constr = {
        left_type  = a.inferred_type;
        right_type = Type.Bool;
        error_info = a.parser_info
      } in
      compute_constraints (constr :: acc) (a :: tail)
  | {expr = Neg a; _} :: tail ->
      (* Unitary integer operation *)
      let constr = {
        left_type  = a.inferred_type;
        right_type = Type.Bool;
        error_info = a.parser_info
      } in
      compute_constraints (constr :: acc) (a :: tail)
  | {expr = If (cond, true_expr, false_expr); _} as ae :: tail ->
      (* The condition must be boolean *)
      let cond_constr = {
        left_type  = cond.inferred_type;
        right_type = Type.Bool;
        error_info = cond.parser_info
      } in
      (* The two expressions must have matching types, each of
       * which match the type variable which represents the
       * conditional result. *)
      let true_constr = {
        left_type  = true_expr.inferred_type;
        right_type = ae.inferred_type;
        error_info = true_expr.parser_info
      } in
      let false_constr = {
        left_type  = false_expr.inferred_type;
        right_type = ae.inferred_type;
        error_info = false_expr.parser_info
      } in
      compute_constraints (cond_constr :: true_constr :: false_constr :: acc)
        (cond :: true_expr :: false_expr :: tail)
  | ({expr = Let    (fun_binding, arg_bindings, eq_expr, in_expr); _} as ae) :: tail
  | ({expr = LetRec (fun_binding, arg_bindings, eq_expr, in_expr); _} as ae) :: tail ->
      (* When annotating the expression tree we  plugged in a dummy typevar as the
       * inferred type of this expression, so now we need to constrain that typevar to
       * match the type of in_expr. *)
      let expr_constr = {
        left_type  = ae.inferred_type;
        right_type = in_expr.inferred_type;
        error_info = ae.parser_info
      } in
      (* In general, a let-binding has an "arrow" type of the form
       * 'a -> 'b -> ... -> 'n.  We can construct this type by a right-fold
       * over the types of the arguments, and then add a constraint to require
       * that the type variable for the let-binding must take this form. *)
      (* FIXME: this may be problematic--if we fail to unify this constraint,
       * the error message will be weak.  It would be better to impose the
       * arrow condition from within [annotate_let]. *)
      let arrow_type = List.fold_right
        (fun arg acc -> Type.Arrow (arg.bind_type, acc))
        arg_bindings
        eq_expr.inferred_type
      in
      let arrow_constr = {
        left_type  = fun_binding.bind_type;
        right_type = arrow_type;
        error_info = ae.parser_info
      } in
      compute_constraints (expr_constr :: arrow_constr :: acc) (eq_expr :: in_expr :: tail)
  | {expr = External (fun_binding, fun_ext_impl, in_expr); _} as ae :: tail ->
      (* When annotating the expression tree we  plugged in a dummy typevar as the
       * inferred type of this expression, so now we need to constrain that typevar to
       * match the type of in_expr. *)
      let constr = {
        left_type  = ae.inferred_type;
        right_type = in_expr.inferred_type;
        error_info = ae.parser_info
      } in
      compute_constraints (constr :: acc) (in_expr :: tail)
  | {expr = Apply (fun_expr, args_exprs); _} as ae :: tail ->
      (* We need to have an arrow type in order to carry out function application *)
      let arrow_type = List.fold_right
        (fun arg acc -> Type.Arrow (arg.inferred_type, acc))
        args_exprs
        ae.inferred_type
      in
      let arrow_constr = {
        left_type  = fun_expr.inferred_type;
        right_type = arrow_type;
        error_info = fun_expr.parser_info
      } in
      compute_constraints (arrow_constr :: acc) ((fun_expr :: args_exprs ) @ tail)


let print_constraints (constraints : constraint_t list) =
  List.iter
    (fun constr -> Printf.printf "%s == %s\n"
      (Type.string_of_type constr.left_type) (Type.string_of_type constr.right_type))
    constraints


let rec apply_substs (substs : Typing_unify.subst_t list) (aexpr : aexpr_t) =
	(* Apply substitutions on an annotated expression *)
  let sub      = apply_substs substs in
	(* Apply substitutions on a type *)
  let sub_type = Typing_unify.apply_substitutions substs in
	let aexpr = {aexpr with inferred_type = sub_type aexpr.inferred_type} in
  match aexpr with
  | {expr = Unit; _}
  | {expr = Bool _; _}
  | {expr = Int _; _}
	| {expr = Var _; _} -> aexpr

  | {expr = Eq (a, b); _}      -> {aexpr with expr = Eq      (sub a, sub b)}
  | {expr = Neq (a, b); _}     -> {aexpr with expr = Neq     (sub a, sub b)}
  | {expr = Leq (a, b); _}     -> {aexpr with expr = Leq     (sub a, sub b)}
  | {expr = Geq (a, b); _}     -> {aexpr with expr = Geq     (sub a, sub b)}
  | {expr = Less (a, b); _}    -> {aexpr with expr = Less    (sub a, sub b)}
  | {expr = Greater (a, b); _} -> {aexpr with expr = Greater (sub a, sub b)}
  | {expr = Add (a, b); _}     -> {aexpr with expr = Add     (sub a, sub b)}
  | {expr = Sub (a, b); _}     -> {aexpr with expr = Sub     (sub a, sub b)}
  | {expr = Mul (a, b); _}     -> {aexpr with expr = Mul     (sub a, sub b)}
  | {expr = Div (a, b); _}     -> {aexpr with expr = Div     (sub a, sub b)}
  | {expr = Mod (a, b); _}     -> {aexpr with expr = Mod     (sub a, sub b)}

	| {expr = Not a; _} -> {aexpr with expr = Not (sub a)}
	| {expr = Neg a; _} -> {aexpr with expr = Neg (sub a)}

	| {expr = If (a, b, c); _} -> {aexpr with expr = If (sub a, sub b, sub c)}

	| {expr = Let (fun_binding, arg_bindings, eq_expr, in_expr); _} -> {aexpr with
			expr = Let (
				{fun_binding with bind_type = sub_type fun_binding.bind_type},
				List.map (fun arg -> {arg with bind_type = sub_type arg.bind_type}) arg_bindings,
				sub eq_expr,
				sub in_expr)
		}
	| {expr = LetRec (fun_binding, arg_bindings, eq_expr, in_expr); _} -> {aexpr with
			expr = LetRec (
				{fun_binding with bind_type = sub_type fun_binding.bind_type},
				List.map (fun arg -> {arg with bind_type = sub_type arg.bind_type}) arg_bindings,
				sub eq_expr,
				sub in_expr)
		}
  | {expr = External (fun_binding, fun_ext_impl, in_expr); _} -> {aexpr with
      expr = External (fun_binding, fun_ext_impl, sub in_expr)
    }

	| {expr = Apply (a, b_list); _} -> {aexpr with expr = Apply (sub a, List.map sub b_list)}



(* Determine the types of all expressions using a Damas-Milner algorithm. *)
let infer (parsed_expr : Syntax.t) : aexpr_t =
  let () = Type.reset_type_vars () in
  let annotated_ast = annotate SMap.empty parsed_expr in
  let type_constraints = compute_constraints [] [annotated_ast] in
  let substitutions = Typing_unify.unify type_constraints in
  apply_substs substitutions annotated_ast


