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

(* Implementation of type inference.  This is a straightforward implementation
 * of Algorithm W, extended as appropriate for the ZML syntax. *)


module TVSet = Type.TVSet
module TVMap = Type.TVMap


type expr_t =
  | Unit                                                 (* Unit literal *)
  | Bool of bool                                         (* Boolean literal *)
  | Int of int                                           (* Integer literal *)
  | Var of string                                        (* Bound variable *)
  | If of aexpr_t * aexpr_t * aexpr_t                    (* Conditional expression *)
  | Apply of aexpr_t * aexpr_t                           (* Single-argument function application *)
  | Lambda of bind_t * aexpr_t                           (* Unary lambda definition *)
  | Let of bind_t * aexpr_t * aexpr_t                    (* Let expression *)
  | LetRec of bind_t * aexpr_t * aexpr_t                 (* Recursive let expression *)
  | External of bind_t * string * aexpr_t                (* External function definition *)

and aexpr_t = {
  expr          : expr_t;                (* Expression *)
  inferred_type : Type.t;                (* Inferred type of expression (possibly a typevar) *)
  parser_info   : Syntax.parser_meta_t   (* Additional info from parser regarding this expr *)
}

and bind_t = {
  bind_name : string;
  bind_type : Type.t
}


let rec string_of_typetree (ast : aexpr_t) : string =
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




module type PROG_VAR = sig
  include Set.OrderedType

  val of_string : string -> t
  val to_string : t -> string
end


module ProgVar : PROG_VAR = struct
  type t = string

  let compare = String.compare
  let of_string s = s
  let to_string s = s
end
module PVMap = Map.Make(ProgVar)


type type_scheme_t = Type.type_scheme_t
type type_env_t = type_scheme_t PVMap.t

type subst_t = Type.t TVMap.t
let identity_subst = TVMap.empty


let pseudofunction_if = "__lambda_cond"


let builtin_env = 
  (* if/then/else conditionals are typed by treating them like application
   * of a function with type "val __lambda_cond : bool -> 'a -> 'a -> 'a". *)
  let pseudofunction_if_ts =
    let tv = TypeVar.fresh () in
    Type.ForAll (TVSet.singleton tv,
      Type.Arrow (Type.Bool,
        Type.Arrow (Type.Var tv,
          Type.Arrow (Type.Var tv, Type.Var tv))))
  in
  List.fold_left
    (fun acc (builtin, ts) -> PVMap.add (ProgVar.of_string builtin) ts acc)
    PVMap.empty
    ((pseudofunction_if, pseudofunction_if_ts) :: Builtins.type_env)


(** [apply_subst_type subst tp] applies a type variable substitution to a type. *)
let rec apply_subst_type (subst : subst_t) (tp : Type.t) : Type.t =
  match tp with
  | Type.Unit | Type.Bool | Type.Int ->
      tp
  | Type.Var tv ->
      begin try TVMap.find tv subst with Not_found -> tp end
  | Type.Arrow (tp1, tp2) ->
      Type.Arrow (apply_subst_type subst tp1, apply_subst_type subst tp2)
  | Type.Array tp ->
      Type.Array (apply_subst_type subst tp)


(** [free_type_vars_type tp] computes the set of free type variables in the given type. *)
let free_type_vars_type (tp : Type.t) : TVSet.t =
  let rec ftv acc x =
    match x with
    | Type.Unit | Type.Bool | Type.Int ->
        acc
    | Type.Var tv ->
        TVSet.add tv acc
    | Type.Arrow (tp1, tp2) ->
        let acc' = ftv acc tp1 in
        ftv acc' tp2
    | Type.Array tp ->
        ftv acc tp
  in
  ftv TVSet.empty tp


(** [apply_subst_scheme subst scheme] applies a type variable substitution to a
  * type scheme. *)
let apply_subst_scheme (subst : subst_t) (scheme : type_scheme_t) : type_scheme_t =
  let Type.ForAll (univ_quant, tp) = scheme in
  (* Avoid substituting the bound variables *)
  let subst' = TVMap.filter (fun tv _ -> not (TVSet.mem tv univ_quant)) subst in
  Type.ForAll (univ_quant, apply_subst_type subst' tp)


(** [free_type_vars_scheme scheme] computes the set of all free type variables
  * in the given type scheme. *)
let free_type_vars_scheme (scheme : type_scheme_t) : TVSet.t =
  let Type.ForAll (univ_quant, tp) = scheme in
  TVSet.diff (free_type_vars_type tp) univ_quant


(** [apply_subst_env subst env] applies a type variable substitution to a typing
  * environment. *)
let apply_subst_env (subst : subst_t) (env : type_env_t) : type_env_t =
  PVMap.map (fun ts -> apply_subst_scheme subst ts) env


(** [free_type_vars_env env] computes the set of all free type variables in the
  * given typing environment. *)
let free_type_vars_env (env : type_env_t) : TVSet.t =
  PVMap.fold
    (fun pv ts acc -> TVSet.union acc (free_type_vars_scheme ts))
    env
    TVSet.empty


(** [compose_subst outer inner] generates a new substitution [s] such that application of [s]
  * is equivalent to application of [inner] followed by application of [outer]. *)
let compose_subst (outer : subst_t) (inner : subst_t) : subst_t =
  TVMap.merge
    (fun tv tp_inner_opt tp_outer_opt ->
      begin match tp_inner_opt, tp_outer_opt with
      | _, Some tp_outer ->
          Some tp_outer
      | tp_inner_opt, None ->
          tp_inner_opt
      end)
    (TVMap.map (fun tp -> apply_subst_type outer tp) inner)
    outer


type constraint_t = {
  (* The type of a constraint: the term on the left must unify with
   * the type on the right.  [error_info] provides the positions from the
   * source file which should be associated with this constraint for
   * the purpose of generating error messages. *)
  left_type  : Type.t;
  right_type : Type.t;
  error_info : Syntax.parser_meta_t
}

exception Unification_failure of constraint_t
exception Unification_occurs_check_failure


(** [unify constr] generates a type variable substitution which unifies the
  * given constraint.  [Unification_failure] is raised upon failure. *)
let rec unify (constr : constraint_t) : subst_t =
  match constr.left_type, constr.right_type with
  | (Type.Unit, Type.Unit) | (Type.Bool, Type.Bool) | (Type.Int, Type.Int) ->
      identity_subst
  | (Type.Var a, Type.Var b) when a = b ->
      identity_subst
  | (Type.Var a, tp) | (tp, Type.Var a) ->
      if TVSet.mem a (free_type_vars_type tp) then
        (* occurs check failure *)
        raise (Unification_failure constr)
      else
        TVMap.singleton a tp
  | (Type.Arrow (left1, right1), Type.Arrow (left2, right2)) ->
      (* FIXME: error message will be misleading here because the
       * error info is wrong *)
      let left_constr = {
        left_type  = left1;
        right_type = left2;
        error_info = constr.error_info
      } in 
      let s1 = unify left_constr in
      let right_constr = {
        left_type  = apply_subst_type s1 right1;
        right_type = apply_subst_type s1 right2;
        error_info = constr.error_info
      } in
      let s2 = unify right_constr in
      compose_subst s1 s2
  | (Type.Array a, Type.Array b) ->
      unify {left_type = a; right_type = b; error_info = constr.error_info}
  | (Type.Unit, _) | (Type.Bool, _) | (Type.Int, _)
  | (Type.Arrow _, _) | (Type.Array _, _) ->
      raise (Unification_failure constr)


(** [generalize env tp] generalizes a type to a type scheme, as is necessary
  * for the implementation of polymorphic-let. *)
let generalize (env : type_env_t) (tp : Type.t) : type_scheme_t =
  let unconstrained = TVSet.diff (free_type_vars_type tp) (free_type_vars_env env) in
  Type.ForAll (unconstrained, tp)


(** [instantiate scheme] instantiates fresh type variables for a type scheme,
  * yielding a concrete type. *)
let instantiate (scheme : type_scheme_t) : Type.t =
  let Type.ForAll (univ_quant, tp) = scheme in
  let fresh_subst = TVSet.fold
    (fun tv acc -> TVMap.add tv (Type.Var (TypeVar.fresh ())) acc)
    univ_quant
    TVMap.empty
  in
  apply_subst_type fresh_subst tp


exception Unbound_value of string * Syntax.parser_meta_t


(* Damas-Milner's Algorithm W.  Loosely following the implementation described in
 * Martin Grabmüller's "Algorithm W Step-by-Step", using the natural extensions
 * for ZML syntax.
 *
 * @param env           environment in which the expression is evaluated; maps bindings to types
 * @param untyped_expr  expression to be type-checked
 *
 * @return tuple of ([subst], [typed_expr]), where:
 *         [subst] is a substitution formed by the unification process
 *         [typed_expr] is the fully-typed expression
 *
 * @raise Typing_unify.Unification_failure if the expression is not well-typed *)
let rec algorithm_w (env : type_env_t) (untyped_expr : Syntax.t)
    : subst_t * aexpr_t =
  match untyped_expr.Syntax.expr with
  | Syntax.Unit ->
      (identity_subst, {
        expr          = Unit;
        inferred_type = Type.Unit;
        parser_info   = untyped_expr.Syntax.parser_info})
  | Syntax.Bool a ->
      (identity_subst, {
        expr          = Bool a;
        inferred_type = Type.Bool;
        parser_info   = untyped_expr.Syntax.parser_info})
  | Syntax.Int a ->
      (identity_subst, {
        expr          = Int a;
        inferred_type = Type.Int;
        parser_info   = untyped_expr.Syntax.parser_info})
  | Syntax.Var v ->
      begin try
        let ts = PVMap.find (ProgVar.of_string v) env in
        (identity_subst, {
          expr          = Var v;
          inferred_type = instantiate ts;
          parser_info   = untyped_expr.Syntax.parser_info})
      with Not_found ->
        raise (Unbound_value (v, untyped_expr.Syntax.parser_info))
      end
  | Syntax.Apply (func, arg) ->
      let fresh_type = Type.Var (TypeVar.fresh ()) in
      let func_subst, func_typed_expr =
        algorithm_w env func
      in
      let arg_subst, arg_typed_expr =
        algorithm_w (apply_subst_env func_subst env) arg
      in
      let unify_subst = unify {
        left_type  = (apply_subst_type arg_subst func_typed_expr.inferred_type);
        right_type = (Type.Arrow (arg_typed_expr.inferred_type, fresh_type));
        error_info = untyped_expr.Syntax.parser_info
      } in
      let subst = compose_subst unify_subst (compose_subst arg_subst func_subst) in
      let tp = apply_subst_type unify_subst fresh_type in
      (subst, {
        expr          = Apply (func_typed_expr, arg_typed_expr);
        inferred_type = tp;
        parser_info   = untyped_expr.Syntax.parser_info})
  | Syntax.If (cond, true_expr, false_expr) ->
      (* For the purpose of typing, "if" can be treated as application of function with type
       * "bool -> 'a -> 'a -> 'a".  After application of Algorithm W, the resulting expression is
       * type-correct but not behaviorally-correct (it does not capture lazy evaluation semantics of
       * true_expr and false_expr), so we immediately rewrite back into an "if" form. *)
      let pseudo_expr =
        { Syntax.expr = Syntax.Apply (
          { Syntax.expr = Syntax.Apply (
            { Syntax.expr = Syntax.Apply (
              { Syntax.expr = Syntax.Var pseudofunction_if;
                (* FIXME: pseudofunction_if is a fake function... not sure if there's actually
                 * anything appropriate to use for parser_info. *)
                Syntax.parser_info = untyped_expr.Syntax.parser_info },
              cond);
              Syntax.parser_info = cond.Syntax.parser_info },
            true_expr);
            Syntax.parser_info = true_expr.Syntax.parser_info },
          false_expr);
          Syntax.parser_info = false_expr.Syntax.parser_info }
      in
      let subst, pseudo_typed_expr = algorithm_w env pseudo_expr in
      begin match pseudo_typed_expr with
      | { expr = Apply (
          { expr = Apply (
            { expr = Apply (
              { expr = Var _; _ }, cond_typed_expr); _ },
            true_typed_expr); _ },
          false_typed_expr); _ } ->
          (subst, {
            expr          = If (cond_typed_expr, true_typed_expr, false_typed_expr);
            inferred_type = pseudo_typed_expr.inferred_type;
            parser_info   = untyped_expr.Syntax.parser_info})
      | _ ->
          assert false
      end
  | Syntax.Lambda (x, body) ->
      let x_tv     = TypeVar.fresh () in
      let x_tp     = Type.Var x_tv in
      let body_env = PVMap.add (ProgVar.of_string x) (Type.ForAll (TVSet.empty, x_tp)) env in
      let body_subst, body_typed_expr = algorithm_w body_env body in
      let arg_tp = apply_subst_type body_subst x_tp in
      (body_subst, {
        expr = Lambda ({bind_name = x; bind_type = arg_tp}, body_typed_expr);
        inferred_type = Type.Arrow (arg_tp, body_typed_expr.inferred_type);
        parser_info   = untyped_expr.Syntax.parser_info})
  | Syntax.Let (x, body, scope) ->
      let body_subst, body_typed_expr = algorithm_w env body in
      let x_generalized_type = generalize (apply_subst_env body_subst env) body_typed_expr.inferred_type in
      let env'      = PVMap.add (ProgVar.of_string x) x_generalized_type env in
      let scope_env = apply_subst_env body_subst env' in
      let scope_subst, scope_typed_expr = algorithm_w scope_env scope in
      let subst = compose_subst body_subst scope_subst in
      (subst, {
        expr = Let (
          {bind_name = x; bind_type = body_typed_expr.inferred_type},
          body_typed_expr,
          scope_typed_expr);
        inferred_type = scope_typed_expr.inferred_type;
        parser_info = untyped_expr.Syntax.parser_info})
  | Syntax.LetRec (x, body, scope) ->
      (* Since [x] may recur in the body, we have to bind it in the environment.  Generate a new
       * type variable for this purpose. *)
      let fresh_type = TypeVar.fresh () in
      let body_env   = PVMap.add (ProgVar.of_string x)
        (Type.ForAll (TVSet.empty, Type.Var fresh_type)) env in
      let body_subst, body_typed_expr = algorithm_w body_env body in
      (* In general [body_typed_expr] will have embedded dependencies on the type variable
       * we just introduced.  Using the constraint that type(x) == type(body), we can now run
       * Algorithm W again without introducing an unnecessary type var.
       * FIXME: this is probably a hack... how do the pros do it? *)
      let body_env = PVMap.add (ProgVar.of_string x)
        (Type.ForAll (TVSet.empty, body_typed_expr.inferred_type)) env in
      let body_subst, body_typed_expr = algorithm_w body_env body in
      (* From here on out it's just like non-recursive let. *)
      let x_generalized_type = generalize (apply_subst_env body_subst env) body_typed_expr.inferred_type in
      let env'      = PVMap.add (ProgVar.of_string x) x_generalized_type env in
      let scope_env = apply_subst_env body_subst env' in
      let scope_subst, scope_typed_expr = algorithm_w scope_env scope in
      let subst = compose_subst body_subst scope_subst in
      (subst, {
        expr = LetRec (
          {bind_name = x; bind_type = body_typed_expr.inferred_type},
          body_typed_expr,
          scope_typed_expr);
        inferred_type = scope_typed_expr.inferred_type;
        parser_info = untyped_expr.Syntax.parser_info})
  | Syntax.External (name, ts, asm_name, scope) ->
      let env' = PVMap.add (ProgVar.of_string name) ts env in
      let subst, typed_scope_expr = algorithm_w env' scope in
      (subst, {
        expr = External (
          {bind_name = name; bind_type = instantiate ts},
          asm_name,
          typed_scope_expr);
        inferred_type = typed_scope_expr.inferred_type;
        parser_info = untyped_expr.Syntax.parser_info})



let infer (parsed_expr : Syntax.t) : aexpr_t =
  let () = TypeVar.reset_vars () in
  let _, typed_ast = algorithm_w builtin_env parsed_expr in

  (* Now that typing is complete, inject External definitions for all
   * the built-in functions. *)
  let bogus_parser_info = {
    Syntax.range =
      {Syntax.fr_start = Lexing.dummy_pos; Syntax.fr_end = Lexing.dummy_pos};
    Syntax.type_annot = None
  } in
  List.fold_left 
    (fun ast (asm_id, ts) -> {
      expr = External (
        {bind_name = asm_id; bind_type = instantiate ts},
        Builtins.asm_name_of_id asm_id,
        ast);
      inferred_type = ast.inferred_type;
      parser_info = bogus_parser_info
    })
    typed_ast
    Builtins.type_env


