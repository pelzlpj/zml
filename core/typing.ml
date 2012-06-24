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
exception Incorrect_args of string * Syntax.parser_meta_t

exception Duplicate_argument_inner of string
exception Duplicate_argument of string * Syntax.parser_meta_t


module SMap = Map.Make(String)
module SSet = Set.Make(String)


(* Exceptionless variant of Map.find. *)
let smap_find x m =
  try Some (SMap.find x m)
  with Not_found -> None


module Int = struct
  type t = int
  let compare e1 e2 = if e1 < e2 then -1 else if e1 > e2 then 1 else 0
end
module IMap = Map.Make(Int)


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
  | ArrayMake of aexpr_t * aexpr_t                       (* Array constructor *)
  | ArrayGet of aexpr_t * aexpr_t                        (* Array lookup *)
  | ArraySet of aexpr_t * aexpr_t * aexpr_t              (* Array mutate *)


and aexpr_t = {
  expr          : expr_t;                (* Expression *)
  inferred_type : Type.t;                (* Inferred type of expression (possibly a typevar) *)
  parser_info   : Syntax.parser_meta_t   (* Additional info from parser regarding this expr *)
}

and bind_t = {
  bind_name : string;
  bind_type : Type.t
}


(* Assign program-unique identifiers to the type variables in a single type expression. *)
let rename_single_constraint_typevars (type_expr : Type.t) : Type.t =
  let rec aux rename_context te =
    match te with
    | Type.Unit | Type.Bool | Type.Int ->
        (rename_context, te)
    | Type.Arrow (a, b) ->
        let a_context, a'  = aux rename_context a in
        let ab_context, b' = aux a_context b in
        (ab_context, Type.Arrow (a', b'))
    | Type.Array a ->
        let context, a' = aux rename_context a in
        (context, Type.Array a')
    | Type.Var a ->
        begin try
          (rename_context, IMap.find a rename_context)
        with Not_found ->
          let var_a = Type.make_type_var () in
          (IMap.add a var_a rename_context, var_a)
        end
  in
  snd (aux IMap.empty type_expr)


(* Recursively examine the AST.  If the AST contains user-defined type constraints, rewrite the
 * constraint equations using program-unique type variable identifiers.  (This is necessary because
 * a type variable like ['a] has a scope which is local to a subexpression, and it's incorrect to
 * assume that ['a] is the *same* type variable across the entire program.  The type unification
 * algorithm can collapse type variables when appropriate.) *)
let rec rename_constraint_typevars (parsed_expr : Syntax.t) : Syntax.t =
  let expr  = parsed_expr.Syntax.expr in
  let annot = parsed_expr.Syntax.parser_info.Syntax.type_annot in
  let renamed_expr =
    match expr with
    | Syntax.Unit | Syntax.Bool _ | Syntax.Int _ | Syntax.Var _ ->
        expr
    | Syntax.Eq (a, b) ->
        Syntax.Eq (rename_constraint_typevars a, rename_constraint_typevars b)
    | Syntax.Neq (a, b) ->
        Syntax.Neq (rename_constraint_typevars a, rename_constraint_typevars b)
    | Syntax.Leq (a, b) ->
        Syntax.Leq (rename_constraint_typevars a, rename_constraint_typevars b)
    | Syntax.Geq (a, b) ->
        Syntax.Geq (rename_constraint_typevars a, rename_constraint_typevars b)
    | Syntax.Less (a, b) ->
        Syntax.Less (rename_constraint_typevars a, rename_constraint_typevars b)
    | Syntax.Greater (a, b) ->
        Syntax.Greater (rename_constraint_typevars a, rename_constraint_typevars b)
    | Syntax.Add (a, b) ->
        Syntax.Add (rename_constraint_typevars a, rename_constraint_typevars b)
    | Syntax.Sub (a, b) ->
        Syntax.Sub (rename_constraint_typevars a, rename_constraint_typevars b)
    | Syntax.Mul (a, b) ->
        Syntax.Mul (rename_constraint_typevars a, rename_constraint_typevars b)
    | Syntax.Div (a, b) ->
        Syntax.Div (rename_constraint_typevars a, rename_constraint_typevars b)
    | Syntax.Mod (a, b) ->
        Syntax.Mod (rename_constraint_typevars a, rename_constraint_typevars b)
    | Syntax.Not a ->
        Syntax.Not (rename_constraint_typevars a)
    | Syntax.Neg a ->
        Syntax.Neg (rename_constraint_typevars a)
    | Syntax.If (a, b, c) ->
        Syntax.If (rename_constraint_typevars a, rename_constraint_typevars b,
          rename_constraint_typevars c)
    | Syntax.Let (a, b, eq_expr, in_expr) ->
        Syntax.Let (a, b, rename_constraint_typevars eq_expr, rename_constraint_typevars in_expr)
    | Syntax.LetRec (a, b, eq_expr, in_expr) ->
        Syntax.LetRec (a, b, rename_constraint_typevars eq_expr, rename_constraint_typevars in_expr)
    | Syntax.External (a, tp, b, in_expr) ->
        Syntax.External (a, rename_single_constraint_typevars tp, b, rename_constraint_typevars in_expr)
    | Syntax.Apply (a, b_list) ->
        Syntax.Apply (rename_constraint_typevars a, List.map rename_constraint_typevars b_list)
    | Syntax.ArrayGet (a, b) ->
        Syntax.ArrayGet (rename_constraint_typevars a, rename_constraint_typevars b)
    | Syntax.ArraySet (a, b, c) ->
        Syntax.ArraySet (rename_constraint_typevars a, rename_constraint_typevars b,
          rename_constraint_typevars c)
  in 
  let renamed_annot =
    match annot with
    | None ->
        annot
    | Some te ->
        Some (rename_single_constraint_typevars te)
  in {
    Syntax.expr        = renamed_expr;
    Syntax.parser_info = { parsed_expr.Syntax.parser_info with Syntax.type_annot = renamed_annot }
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
  | Syntax.Apply (a, args) ->
      (* Special case: [array_make] is a predefined library function.  It results in a call
       * to [zml_array_create], which relies on reference/value type tracking in order to
       * allocate an array of the correct type.  Consequently it is not appropriate to
       * define this function via the standard "external" interface.
       *
       * FIXME: this isn't sufficient, because [array_make] could just as easily be treated
       * as first-class and called via unknown-function application. *)
      begin match a.Syntax.expr with
      | Syntax.Var "array_make" ->
          begin match args with
          | [len; value] -> 
              let value_aexpr = annotate env value in {
              expr          = ArrayMake (annotate env len, value_aexpr);
              inferred_type = Type.Array (value_aexpr.inferred_type);
              parser_info
            }
          | _ ->
              raise (Incorrect_args ("array_make", parser_info))
          end
      | _ -> {
          expr          = Apply (annotate env a, List.map (annotate env) args);
          inferred_type = Type.make_type_var ();
          parser_info
        }
      end
  | Syntax.ArrayGet (a, index) -> {
      expr          = ArrayGet (annotate env a, annotate env index);
      inferred_type = Type.make_type_var ();
      parser_info
    }
  | Syntax.ArraySet (a, index, value) -> {
      expr          = ArraySet (annotate env a, annotate env index, annotate env value);
      inferred_type = Type.Unit;
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
  | {expr = ArrayMake (len, value); _} as ae :: tail ->
      (* The length must be an int *)
      let len_constr = {
        left_type  = len.inferred_type;
        right_type = Type.Int;
        error_info = len.parser_info
      } in
      (* The array must contain elements of the proper type *)
      let container_constr = {
        left_type  = ae.inferred_type;
        right_type = Type.Array value.inferred_type;
        error_info = ae.parser_info
      } in
      compute_constraints (len_constr :: container_constr :: acc) (len :: value :: tail)
  | {expr = ArrayGet (arr, index); _} as ae :: tail ->
      (* The index must be an int *)
      let index_constr = {
        left_type  = index.inferred_type;
        right_type = Type.Int;
        error_info = index.parser_info
      } in
      (* The array must contain elements of the proper type *)
      let container_constr = {
        left_type  = arr.inferred_type;
        right_type = Type.Array ae.inferred_type;
        error_info = arr.parser_info
      } in
      compute_constraints (index_constr :: container_constr :: acc) (arr :: index :: tail)
  | {expr = ArraySet (arr, index, value); _} as ae :: tail ->
      (* The index must be an int *)
      let index_constr = {
        left_type  = index.inferred_type;
        right_type = Type.Int;
        error_info = index.parser_info
      } in
      (* The array must contain elements of the proper type *)
      let container_constr = {
        left_type  = arr.inferred_type;
        right_type = Type.Array value.inferred_type;
        error_info = arr.parser_info
      } in
      (* The assignment operation must return unit *)
      let op_constr = {
        left_type  = ae.inferred_type;
        right_type = Type.Unit;
        error_info = ae.parser_info
      } in
      compute_constraints (index_constr :: container_constr :: op_constr :: acc)
        (arr :: index :: value :: tail)


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
  
  | {expr = ArrayMake (len, value); _}     -> {aexpr with expr = ArrayMake (sub len, sub value)}
  | {expr = ArrayGet (a, index); _}        -> {aexpr with expr = ArrayGet (sub a, sub index)}
  | {expr = ArraySet (a, index, value); _} -> {aexpr with expr = ArraySet (sub a, sub index, sub value)}


(* Determine the types of all expressions using a Damas-Milner algorithm. *)
let infer (parsed_expr : Syntax.t) : aexpr_t =
  let () = Type.reset_type_vars () in
  let type_renamed_ast = rename_constraint_typevars parsed_expr in
  let annotated_ast    = annotate SMap.empty type_renamed_ast in
  let type_constraints = compute_constraints [] [annotated_ast] in
  let substitutions    = Typing_unify.unify type_constraints in
  apply_substs substitutions annotated_ast


