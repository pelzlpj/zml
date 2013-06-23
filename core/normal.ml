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



(* Conversion to a normalized form.  The following operations are applied:
 *
 *    * Alpha conversion: bound variables are renamed using
 *      whole-program-unique integer ids.
 *
 *    * All nested (i.e. intermediate) expressions are bound to temporary
 *      variables via let-binding.
 *
 *    * Boolean comparison expressions and if-conditional expressions are
 *      converted into a combined integer comparison and branch, to more closely
 *      match assembly semantics.  The set of conditional tests is reduced
 *      to simple integer equality and "less than" comparison.
 *
 *    * Boolean "false" and "true" are converted to 0 and 1, respectively.
 *
 *    * Multi-argument function definitions are recognized as first-class
 *      entities, so they more closely match calling conventions for
 *      the target virtual machines.
 *
 * FIXME: polymorphic builtins probably need to be recognized within this module, 
 * so that an appropriate implementation can be selected... i.e. "__zml_op_pseudofunc_poly_eq"
 * should be rewritten as something like "__zml_array_eq" when operating on
 * an array type.
 *)

open Printf


(* The type of program-unique variable identifiers. *)
module VarID = struct
  (* Note: for ease of comparing an AST with the original source, it would be helpful if these
   * identifiers included the original string variable names... *)
  type t = {id : int; tp : Type.t}
  let compare e1 e2 = if e1.id < e2.id then -1 else if e1.id > e2.id then 1 else 0
  let to_string     (x : t) : string = sprintf "v%d" x.id
  let to_int_string (x : t) : string = sprintf "%d"  x.id
end

type var_t = VarID.t

(* Used in module Function. *)
module VMap = Map.Make(VarID)
module VSet = Set.Make(VarID)

(* Used for mapping string variable names to var_t variable ids *)
module SMap = Map.Make(String)


type cond_t =
  | IfEq    (* Branching on integer equality test *)
  | IfLess  (* Branching on integer ordering test *)


type t =
  | Unit                                              (* Unit literal *)
  | Int of int                                        (* Integer constant *)
  | Conditional of cond_t * var_t * var_t * t * t     (* Conditional form *)
  | Var of var_t                                      (* Bound variable reference *)
  | Let of var_t * t * t                              (* Let binding for a variable *)
  | LetFun of string * var_t * (var_t list) * t * t   (* Let binding for a function definition *)
  | External of string * var_t * string * int * t     (* External (assembly passthrough) function definition *)
  | Apply of var_t * (var_t list)                     (* Function application *)


let rec string_of_normal (ast : t) : string =
  match ast with
  | Unit -> "()"
  | Int i -> string_of_int i
  | Conditional (cond, a, b, c, d) ->
      let op_s =
        match cond with
        | IfEq   -> "="
        | IfLess -> "<"
      in
      sprintf "if %s %s %s then\n    %s\nelse\n    %s\n"
      (VarID.to_string a) op_s (VarID.to_string b) (string_of_normal c) (string_of_normal d)
  | Var a ->
      VarID.to_string a
  | Let (a, b, c) ->
      sprintf "let %s = %s in\n%s" (VarID.to_string a) (string_of_normal b) (string_of_normal c)
  | LetFun (name, id, args, def, use) ->
      sprintf "let %s_%s %s = %s in\n%s" name (VarID.to_string id)
        (String.concat " " (List.map (fun x -> VarID.to_string x) args))
        (string_of_normal def) (string_of_normal use)
  | External (name, id, ext_impl, _, use) ->
      sprintf "external %s_%s = %s in\n%s" name (VarID.to_string id) ext_impl (string_of_normal use)
  | Apply (f, args) ->
      sprintf "apply(%s %s)" (VarID.to_string f)
        (String.concat " " (List.map (fun x -> VarID.to_string x) args))



(* This type is used to associate string variable names with the program-unique
 * var_t variable identifiers. *)
type rename_context_t = var_t SMap.t

(* This ID will never be assigned; it is reserved for use by [Function.extract_functions]. *)
let reserved_main_id = 0

let var_count = ref (reserved_main_id + 1)

let reset_vars () =
  var_count := (reserved_main_id + 1)

(* Get the next free variable id. *)
let free_var () =
  let var_id = !var_count in
  let () = incr var_count in
  var_id

(* Get the next free variable id, binding [name] to the id via the
 * [renames] map. *)
let free_named_var renames name tp =
  let x = {VarID.id = free_var (); VarID.tp = tp} in
  (SMap.add name x renames, x)


(* Given an arrow type, compute the number of arguments the function consumes. *)
let rec count_arrow_type_args ?(acc=0) x =
  match x with
  | Type.Arrow (a, b) ->
      count_arrow_type_args ~acc:(acc + 1) b
  | _ ->
      acc


module TLambda = Typing.TypedLambda
module TNode   = Typing.TypedNode

(* If necessary, insert a let expression which binds a temporary variable to an intermediate
 * expression. (If the expression is already a simple variable, the let expression is
 * considered unnecessary and is omitted.) *)
let rec insert_let
  (renames : rename_context_t)      (* Associates string variable names with var_t's *)
  (aexpr   : TLambda.t TNode.t)     (* Expression to be bound *)
  (f : var_t -> t)                  (* Constructs an expression which uses the new binding *)
    : t =
  begin match aexpr.TNode.expr with
  | TLambda.Var var_name ->
      (* This lookup never fails, because the type checker verified that the variable is bound. *)
      begin try
        f (SMap.find var_name renames)
      with Not_found ->
        let () = Printf.printf "not found: %s\n" var_name in
        raise Not_found
      end
  | _ ->
      let new_var = {VarID.id = free_var (); VarID.tp = aexpr.TNode.inferred_type} in
      let eq_norm = normalize_aux renames aexpr in
      let in_norm = f new_var in
      Let (new_var, eq_norm, in_norm)
  end


(* Convenience function: insert a pair of let expressions via [insert_let], as required when
 * expanding a binary operation.  The let-expressions will bind to value types. *)
and insert_binary_let
  (renames : rename_context_t)
  (a : TLambda.t TNode.t)
  (b : TLambda.t TNode.t)
  (f : var_t -> var_t -> t)
    : t =
  insert_let renames a
    (fun a_binding -> insert_let renames b
      (fun b_binding -> f a_binding b_binding))


(* Normalize an expression of the form "if a < b then true_val else false_val" *)
and normalize_integer_less renames a b true_val false_val =
  insert_binary_let renames a b
    (fun a_binding b_binding -> Conditional (IfLess, a_binding, b_binding, true_val, false_val))

(* Normalize a "let" or "let rec" expression.  Function definitions are differentiated from
 * simple variable bindings. *)
and normalize_let
  (renames : rename_context_t)    (* Variable renaming context for the current expression *)
  ~(is_rec : bool)                (* true iff this is a "let rec" form *)
  (name    : TNode.bind_t)       (* Name of the variable being bound *)
  (eq_expr : TLambda.t TNode.t)      (* Expression being bound to a variable *)
  (in_expr : TLambda.t TNode.t)      (* Expression in which the binding is in scope *)
    : t =
  let in_renames, bind_var =
    free_named_var renames name.TNode.bind_name name.TNode.bind_type
  in
  let in_norm = normalize_aux in_renames in_expr in
  (* If this is a "let rec" form, then the function name may recur in the let-body. *)
  let eq_renames = if is_rec then in_renames else renames in

  (* The parser rewrites "let f x y z = ... in ..." into a form based on unary-let and
   * unary-lambda:
   *
   *    let f =
   *      (fun x ->
   *        (fun y ->
   *          (fun z -> ...)))
   *    in
   *    ...
   *
   * This simplifies typing, but it's a poor match to typical assembly calling conventions.
   * Let-lambda chains are therefore rewritten as multi-argument function definitions, with
   * assistance from [normalize_lambda]. *)
  match eq_expr.TNode.expr with
  | TLambda.Lambda (lambda_arg, lambda_body) ->
      let func_args, func_body = normalize_lambda eq_renames [] lambda_arg lambda_body in
      LetFun (name.TNode.bind_name, bind_var, func_args, func_body, in_norm)
  | _ ->
      let eq_norm = normalize_aux eq_renames eq_expr in
      Let (bind_var, eq_norm, in_norm)


(* Normalize a unary lambda expression.  Lambda chains are coalesced into multi-argument
 * function definitions. *)
and normalize_lambda
  (renames  : rename_context_t)  (* Variable renaming context for the current expression *)
  (args_acc : var_t list)        (* Accumulator for arguments of a multi-argument function (reversed) *)
  (arg      : TNode.bind_t)     (* Argument bound in the lambda body *)
  (body     : TLambda.t TNode.t)    (* Body of the lambda *)
    : (var_t list) * t =         (* Argument list (always nonempty), and function body *)
  (* Allocate a fresh variable for the argument *)
  let body_renames, arg_var =
    free_named_var renames arg.TNode.bind_name arg.TNode.bind_type
  in
  let args_acc' = arg_var :: args_acc in
  match body.TNode.expr with
  | TLambda.Lambda (next_arg, next_body) ->
      normalize_lambda body_renames args_acc' next_arg next_body
  | _ ->
      (List.rev args_acc', normalize_aux body_renames body)


(* Normalize a (possibly multi-argument) function application. This will coalesce as many
 * arguments as possible into a single application, constructing intermediate expressions
 * only when the chain of Apply() operations is broken. *)
and normalize_apply
  (renames : rename_context_t)      (* Variable renaming context for the current expression *)
  (arg_acc : var_t list)            (* Accumulator for applied arguments *)
  (func    : TLambda.t TNode.t)        (* Function being applied *)
  (arg     : TLambda.t TNode.t)        (* Argument to which the function is applied *)
    : t =
  match func.TNode.expr with
  | TLambda.Apply (inner_func, inner_arg) ->
      insert_let renames arg
        (fun arg_var -> normalize_apply renames (arg_var :: arg_acc) inner_func inner_arg)
  | _ ->
      insert_binary_let renames func arg
        (fun bound_func bound_arg ->
          Apply (bound_func, bound_arg :: arg_acc))


(* Normalize an if/then/else conditional.
 *
 * Assembly targets typically provide a combined integer-comparison-and-branch as the basic
 * logical branching construct.  If we explicitly recognize conditionals which match this pattern,
 * then we can often avoid the more general two-step procedure of (1) computing a boolean value
 * for the conditional and then (2) comparing the boolean result to true/false and branching.
 *
 * At some point in the future, it may make more sense to move some of this logic into
 * an optimization pass.  But right now, there aren't really any optimization passes... and
 * this makes the IR and assembly much easier to read. *)
and normalize_if
  (renames : rename_context_t)      (* Variable renaming context for the current expression *)
  (cond_expr : TLambda.t TNode.t)      (* Conditional expression *)
  (true_expr : TLambda.t TNode.t)      (* Expression evaluated if true *)
  (false_expr: TLambda.t TNode.t)      (* Expression evaluated if false *)
    : t =
  match cond_expr.TNode.expr with
  | TLambda.Apply ({TNode.expr = TLambda.Apply (
      {TNode.expr = TLambda.Var op; _}, a); _}, b) when op = Builtins.eq ->
      let true_norm  = normalize_aux renames true_expr in
      let false_norm = normalize_aux renames false_expr in
      insert_binary_let renames a b
        (fun a_binding b_binding ->
          match a.TNode.inferred_type with
          | Type.Unit ->
              (* Unit equality never fails *)
              true_norm
          | Type.Bool | Type.Int ->
              (* Integer value equality test *)
              Conditional (IfEq, a_binding, b_binding, true_norm, false_norm)
          | Type.Arrow _ | Type.Array _ | Type.Var _ ->
              (* If the arrow type resolves to a known function, then this is integer
               * equality (i.e. physical comparison of the function pointers).  If the arrow type
               * resolves to a closure, or if we're considering the array case, then we need to
               * dispatch to the polymorphic structural compare provided by the runtime.
               *
               * If we're looking at a type variable, we'll have to wait until function
               * instantiation before trying to figure out what is meant by "equality". *)
              let cond_var = {VarID.id = free_var (); VarID.tp = Type.Int} in
              let one_var  = {VarID.id = free_var (); VarID.tp = Type.Int} in
              Let (one_var, Int 1,
                Let (cond_var, normalize_aux renames cond_expr,
                  Conditional (IfEq, cond_var, one_var, true_norm, false_norm))))
  | TLambda.Apply ({TNode.expr = TLambda.Apply (
      {TNode.expr = TLambda.Var op; _} as inner_comp, a); _} as outer_comp, b) when op = Builtins.neq ->
      (* Inverting the conditional, making the operation Builtins.eq *)
      let inverse_inner_comp = {inner_comp with TNode.expr = TLambda.Var Builtins.eq} in
      let inverse_outer_comp = {outer_comp with TNode.expr = TLambda.Apply (inverse_inner_comp, a)} in
      let inverse_cond_expr  = TLambda.Apply (inverse_outer_comp, b) in
      (* Swapping true and false branches *)
      normalize_if renames {cond_expr with TNode.expr = inverse_cond_expr} false_expr true_expr
  | TLambda.Apply ({TNode.expr = TLambda.Apply (
      {TNode.expr = TLambda.Var op; _}, a); _}, b) when op = Builtins.leq ->
      let true_norm  = normalize_aux renames true_expr in
      let false_norm = normalize_aux renames false_expr in
      (* Using transformation a <= b --> not (b < a) *)
      normalize_integer_less renames b a false_norm true_norm
  | TLambda.Apply ({TNode.expr = TLambda.Apply (
      {TNode.expr = TLambda.Var op; _}, a); _}, b) when op = Builtins.geq ->
      let true_norm  = normalize_aux renames true_expr in
      let false_norm = normalize_aux renames false_expr in
      (* Using transformation a >= b --> not (a < b) *)
      normalize_integer_less renames a b false_norm true_norm
  | TLambda.Apply ({TNode.expr = TLambda.Apply (
      {TNode.expr = TLambda.Var op; _}, a); _}, b) when op = Builtins.less ->
      let true_norm  = normalize_aux renames true_expr in
      let false_norm = normalize_aux renames false_expr in
      normalize_integer_less renames a b true_norm false_norm
  | TLambda.Apply ({TNode.expr = TLambda.Apply (
      {TNode.expr = TLambda.Var op; _}, a); _}, b) when op = Builtins.greater ->
      let true_norm  = normalize_aux renames true_expr in
      let false_norm = normalize_aux renames false_expr in
      (* Using transformation a > b --> b < a *)
      normalize_integer_less renames b a true_norm false_norm
  | _ ->
      (* General case... if we can't use combined comparison-and-branch, then evaluate
       * the condition explicitly and branch on comparison to "true". *)
      let true_norm  = normalize_aux renames true_expr in
      let false_norm = normalize_aux renames false_expr in
      insert_let renames cond_expr
        (fun cond_binding ->
          let one_binding = {VarID.id = free_var (); VarID.tp = Type.Int} in
          Let (one_binding, Int 1,
            Conditional (IfEq, cond_binding, one_binding, true_norm, false_norm)))
  

(* Convert a type-annotated syntax tree into the normalized form. *)
and normalize_aux
  (renames : rename_context_t)      (* Variable renaming context for the current expression *)
  (aexpr   : TLambda.t TNode.t)        (* Expression to be normalized *)
    : t =
  let expr = aexpr.TNode.expr in
  match expr with
  | TLambda.Unit ->
      Unit
  | TLambda.Bool a ->
      if a then (Int 1) else (Int 0)
  | TLambda.Int n ->
      Int n
  | TLambda.Var var_name ->
      (* If this lookup fails, then the variable is unbound.  This shouldn't happen,
       * as the type-checker would have caught it. *)
      Var (SMap.find var_name renames)
  | TLambda.If (cond_expr, true_expr, false_expr) ->
      normalize_if renames cond_expr true_expr false_expr
  | TLambda.Let (name, eq_expr, in_expr) ->
      normalize_let renames ~is_rec:false name eq_expr in_expr
  | TLambda.LetRec (name, eq_expr, in_expr) ->
      normalize_let renames ~is_rec:true name eq_expr in_expr
  | TLambda.Apply (func, arg) ->
      normalize_apply renames [] func arg
  | TLambda.Lambda (arg, body) ->
      (* Rewriting "fun x y ... -> ..." as "let f x y ... -> ... in f" *)
      let args, combined_body = normalize_lambda renames [] arg body in
      let binding = {VarID.id = free_var (); VarID.tp = aexpr.TNode.inferred_type} in
      LetFun ("__lambda", binding, args, combined_body, Var binding)
  | TLambda.External (name, ext_impl, in_expr) ->
      let arg_count = count_arrow_type_args name.TNode.bind_type in
      let () = assert (arg_count > 0) in
      let (in_renames, binding) = free_named_var renames name.TNode.bind_name name.TNode.bind_type in
      let in_norm = normalize_aux in_renames in_expr in
      External (name.TNode.bind_name, binding, ext_impl, arg_count, in_norm)



(* For the sake of readability, flatten nested let-bindings.  For example,
 *
 *   let x =
 *     let y = expr1 in
 *     let z = expr2 in
 *     expr3
 *   in
 *   expr4
 *
 * is transformed to
 *
 *   let y = expr1 in
 *   let z = expr2 in
 *   let x = expr3 in
 *   expr4
 *
 * All variable ids are program-unique before this transformation is
 * applied, which makes the operation relatively straightforward. *)
let rec flatten (expr : t) : t =
  match expr with
  | Let (x, Let (y, y_eq, y_in), x_in) ->
      flatten (Let (y, y_eq, flatten (Let (x, y_in, x_in))))
  | Let (x, x_eq, x_in) ->
      Let (x, flatten x_eq, flatten x_in)
  | Conditional (cond, a, b, c, d) ->
      Conditional (cond, a, b, flatten c, flatten d)
  | LetFun (x_name, x, args, body, use) ->
      LetFun (x_name, x, args, flatten body, flatten use)
  | e -> e


(* Convert a type-annotated syntax tree into the normalized form. *)
let normalize (aexpr : TLambda.t TNode.t) : t =
  let () = reset_vars () in
  flatten (normalize_aux SMap.empty aexpr)

