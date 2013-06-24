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


open Printf
module TVSet = Type.TVSet
module TVMap = Type.TVMap

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
  error_info : ParserMeta.parser_meta_t
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


exception Unbound_value of string * ParserMeta.parser_meta_t


module type AST_NODE_BASE = sig
  type 'a t
  (** The type of an expression node. *)

  type bind_t
  (** The type of a variable binding. *)

  val get_expr : 'a t -> 'a
  (** [get_expr x] retrieves the expression contained in the given expression node. *)

  val get_parser_info : 'a t -> ParserMeta.parser_meta_t
  (** [get_parser_info x] retrieves the parser metadata contained in the given expression node. *)

  val get_type_constraint : 'a t -> Type.type_scheme_t option
  (** [get_type_constraint x] retrieves the type constraint associated with the 
      given expression node, if any. *)

  val get_name : bind_t -> string
  (** [get_name binding] retrieves the string name under which an expression is bound. *)
end


module type AST_NODE_UNTYPED = sig
  include AST_NODE_BASE

  val make : expr:'a -> parser_info:ParserMeta.parser_meta_t -> 'a t
  (** [make expr parser_info] constructs a new expression node with the given type parser metadata. *)
end


module type AST_NODE_TYPED = sig
  include AST_NODE_BASE

  val make : expr:'a -> inferred_type:Type.t -> parser_info:ParserMeta.parser_meta_t -> 'a t
  (** [make expr tp parser_info] constructs a new expression node
      with the given type and parser metadata. *)

  val get_type : 'a t -> Type.t
  (** [get_type x] retrieves the inferred type of the given expression node. *)

  val make_binding : string -> Type.t -> bind_t
  (** [make_binding name type] constructs a new binding node which associates the
      name with an expression of the given type. *)
end


module type LAMBDA = functor (Node : AST_NODE_BASE) -> sig
  type t =
    | Unit
    | Bool of bool
    | Int of int
    | Var of string
    | If of (t Node.t) * (t Node.t) * (t Node.t)
    | Apply of (t Node.t) * (t Node.t)
    | Lambda of Node.bind_t * (t Node.t)
    | Let of Node.bind_t * (t Node.t) * (t Node.t)
    | LetRec of Node.bind_t * (t Node.t) * (t Node.t)
    | External of Node.bind_t * string * (t Node.t)
end

module Lambda (Node : AST_NODE_BASE) = struct
  type t =
    | Unit
    | Bool of bool
    | Int of int
    | Var of string
    | If of (t Node.t) * (t Node.t) * (t Node.t)
    | Apply of (t Node.t) * (t Node.t)
    | Lambda of Node.bind_t * (t Node.t)
    | Let of Node.bind_t * (t Node.t) * (t Node.t)
    | LetRec of Node.bind_t * (t Node.t) * (t Node.t)
    | External of Node.bind_t * string * (t Node.t)
end

module Make (UntypedNode : AST_NODE_UNTYPED) (TypedNode : AST_NODE_TYPED) = struct

  module ULambda = Lambda(UntypedNode)
  module TLambda = Lambda(TypedNode)


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
  let rec algorithm_w (env : type_env_t) (untyped_expr : ULambda.t UntypedNode.t)
      : subst_t * (TLambda.t TypedNode.t) =
    let parser_info = UntypedNode.get_parser_info untyped_expr in
    match UntypedNode.get_expr untyped_expr with
    | ULambda.Unit ->
        (identity_subst,
          TypedNode.make
            ~expr:TLambda.Unit
            ~inferred_type:Type.Unit
            ~parser_info)
    | ULambda.Bool a ->
        (identity_subst,
          TypedNode.make
            ~expr:(TLambda.Bool a)
            ~inferred_type:Type.Bool
            ~parser_info)
    | ULambda.Int a ->
        (identity_subst,
          TypedNode.make
            ~expr:(TLambda.Int a)
            ~inferred_type:Type.Int
            ~parser_info)
    | ULambda.Var v ->
        begin try
          let ts = PVMap.find (ProgVar.of_string v) env in
          (identity_subst,
            TypedNode.make
              ~expr:(TLambda.Var v)
              ~inferred_type:(instantiate ts)
              ~parser_info)
        with Not_found ->
          raise (Unbound_value (v, parser_info))
        end
    | ULambda.Apply (func, arg) ->
        let fresh_type = Type.Var (TypeVar.fresh ()) in
        let func_subst, func_typed_expr =
          algorithm_w env func
        in
        let arg_subst, arg_typed_expr =
          algorithm_w (apply_subst_env func_subst env) arg
        in
        let unify_subst = unify {
          left_type  = (apply_subst_type arg_subst (TypedNode.get_type func_typed_expr));
          right_type = (Type.Arrow (TypedNode.get_type arg_typed_expr, fresh_type));
          error_info = parser_info
        } in
        let subst = compose_subst unify_subst (compose_subst arg_subst func_subst) in
        let tp = apply_subst_type unify_subst fresh_type in
        (subst,
          TypedNode.make
            ~expr:(TLambda.Apply (func_typed_expr, arg_typed_expr))
            ~inferred_type:tp
            ~parser_info)
    | ULambda.If (cond, true_expr, false_expr) ->
        (* For the purpose of typing, "if" can be treated as application of function with type
         * "bool -> 'a -> 'a -> 'a".  After application of Algorithm W, the resulting expression is
         * type-correct but not behaviorally-correct (it does not capture lazy evaluation semantics of
         * true_expr and false_expr), so we immediately rewrite back into an "if" form. *)
        let pseudo_expr =
          UntypedNode.make ~expr:(ULambda.Apply (
            UntypedNode.make ~expr:(ULambda.Apply (
              UntypedNode.make ~expr:(ULambda.Apply (
                UntypedNode.make ~expr:(ULambda.Var pseudofunction_if)
                  (* FIXME: pseudofunction_if is a fake function... not sure if there's actually
                   * anything appropriate to use for parser_info. *)
                  ~parser_info:parser_info,
                cond))
                ~parser_info:(UntypedNode.get_parser_info cond),
              true_expr))
              ~parser_info:(UntypedNode.get_parser_info true_expr),
            false_expr))
            ~parser_info:(UntypedNode.get_parser_info false_expr)
        in
        let subst, pseudo_typed_expr = algorithm_w env pseudo_expr in
        begin match TypedNode.get_expr pseudo_typed_expr with
        | TLambda.Apply (func0, false_typed_expr) ->
            begin match TypedNode.get_expr func0 with
            | TLambda.Apply (func1, true_typed_expr) ->
                begin match TypedNode.get_expr func1 with
                | TLambda.Apply (func2, cond_typed_expr) ->
                    begin match TypedNode.get_expr func2 with
                    | TLambda.Var _ ->
                        (subst,
                          TypedNode.make
                            ~expr:(TLambda.If (cond_typed_expr, true_typed_expr, false_typed_expr))
                            ~inferred_type:(TypedNode.get_type pseudo_typed_expr)
                            ~parser_info)
                    | _ ->
                        assert false
                    end
                | _ ->
                    assert false
                end
            | _ ->
                assert false
            end
        | _ ->
            assert false
        end
    | ULambda.Lambda (x, body) ->
        let x_tp =
          (* A user-defined type annotation will get added to the environment of the body.
           * This can have the effect of constraining a function so that it is non-polymorphic
           * (i.e. "let id (x : int) = x" should type to "val id : int -> int"). *)
          match parser_info.ParserMeta.type_annot with
          | Some ts ->
              instantiate ts
          | None ->
              Type.Var (TypeVar.fresh ())
        in
        let x_str    = UntypedNode.get_name x in
        let body_env = PVMap.add (ProgVar.of_string x_str) (Type.ForAll (TVSet.empty, x_tp)) env in
        let body_subst, body_typed_expr = algorithm_w body_env body in
        let arg_tp = apply_subst_type body_subst x_tp in
        (body_subst,
          TypedNode.make
            ~expr:(TLambda.Lambda (TypedNode.make_binding x_str arg_tp, body_typed_expr))
            ~inferred_type:(Type.Arrow (arg_tp, TypedNode.get_type body_typed_expr))
            ~parser_info)
    | ULambda.Let (x, body, scope) ->
        let body_subst, body_typed_expr = algorithm_w env body in
        (* If a user-specified type annotation was attached to the let-binding, we unify against
         * this additional constraint before descending into the scope of the let.  If the body
         * of the let is polymorphic, this additional type constraint could make the binding
         * less polymorphic. *)
        let body_subst, body_typed_expr =
          match parser_info.ParserMeta.type_annot with
          | Some constr_ts ->
              let annot_constraint = {
                left_type  = instantiate constr_ts;
                right_type = TypedNode.get_type body_typed_expr;
                error_info = parser_info
              } in
              let constr_subst = unify annot_constraint in
              let constrained_body_typed_expr = TypedNode.make
                ~expr:(TypedNode.get_expr body_typed_expr)
                ~parser_info:(TypedNode.get_parser_info body_typed_expr)
                ~inferred_type:(apply_subst_type constr_subst (TypedNode.get_type body_typed_expr))
              in
              (compose_subst constr_subst body_subst, constrained_body_typed_expr)
          | None ->
              body_subst, body_typed_expr
        in
        let x_generalized_type =
          generalize (apply_subst_env body_subst env) (TypedNode.get_type body_typed_expr)
        in
        let x_str     = UntypedNode.get_name x in
        let env'      = PVMap.add (ProgVar.of_string x_str) x_generalized_type env in
        let scope_env = apply_subst_env body_subst env' in
        let scope_subst, scope_typed_expr = algorithm_w scope_env scope in
        let subst = compose_subst body_subst scope_subst in
				(subst,
					TypedNode.make
						~expr:(TLambda.Let (TypedNode.make_binding x_str (TypedNode.get_type body_typed_expr),
							body_typed_expr, scope_typed_expr))
						~inferred_type:(TypedNode.get_type scope_typed_expr)
						~parser_info)
    | ULambda.LetRec (x, body, scope) ->
        (* Since [x] may recur in the body, we have to bind it in the environment.  Generate a new
         * type variable for this purpose. *)
				let x_str = UntypedNode.get_name x in
        let fresh_type = TypeVar.fresh () in
        let body_env   = PVMap.add (ProgVar.of_string x_str)
          (Type.ForAll (TVSet.empty, Type.Var fresh_type)) env in
        let body_subst, body_typed_expr = algorithm_w body_env body in
        (* In general [body_typed_expr] will have embedded dependencies on the type variable
         * we just introduced.  Using the constraint that type(x) == type(body), we can now run
         * Algorithm W again without introducing an unnecessary type var.
         * FIXME: this is probably a hack... how do the pros do it? *)
        let body_env = PVMap.add (ProgVar.of_string x_str)
          (Type.ForAll (TVSet.empty, TypedNode.get_type body_typed_expr)) env in
        let body_subst, body_typed_expr = algorithm_w body_env body in
        (* From here on out it's just like non-recursive let. *)
        let x_generalized_type =
					generalize (apply_subst_env body_subst env) (TypedNode.get_type body_typed_expr)
				in
        let env'      = PVMap.add (ProgVar.of_string x_str) x_generalized_type env in
        let scope_env = apply_subst_env body_subst env' in
        let scope_subst, scope_typed_expr = algorithm_w scope_env scope in
        let subst = compose_subst body_subst scope_subst in
				(subst,
					TypedNode.make
						~expr:(TLambda.LetRec (TypedNode.make_binding x_str (TypedNode.get_type body_typed_expr),
							body_typed_expr, scope_typed_expr))
						~inferred_type:(TypedNode.get_type scope_typed_expr)
						~parser_info)
    | ULambda.External (name, asm_name, scope) ->
				let ts =
					begin match UntypedNode.get_type_constraint untyped_expr with
					| Some x -> x
					| None   -> assert false
					end
				in
				let name_str = UntypedNode.get_name name in
        let env' = PVMap.add (ProgVar.of_string name_str) ts env in
        let subst, typed_scope_expr = algorithm_w env' scope in
				(subst,
					TypedNode.make
						~expr:(TLambda.External (TypedNode.make_binding name_str (instantiate ts),
							asm_name, typed_scope_expr))
						~inferred_type:(TypedNode.get_type typed_scope_expr)
						~parser_info)

end




