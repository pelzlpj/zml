(* Implementation of type inference, roughly following Algorithm W of
 * Damas and Milner. *)


module SMap = Map.Make(String)
module SSet = Set.Make(String)

(* Exceptionless variant of Map.find. *)
let smap_find x m =
  try
    Some (SMap.find x m)
  with Not_found ->
    None

(* Union of two maps.  If the keys of the maps intersect, then
 * the values from [m1] are selected for the intersecting keys. *)
let smap_union_prefer_first m1 m2 =
  let f key value_m1 value_m2 =
    match value_m1 with
    | Some v1 -> Some v1
    | None ->
        begin match value_m2 with
        | Some v2 -> Some v2
        | None -> assert false
        end
  in
  SMap.merge f m1 m2


(* Type-annotated expressions.  (This does not refer to user-specified
 * annotations, but to the annotations inserted by the compiler during the
 * type inference procedure. *)
type t = {
  parsed_expr   : Syntax.t;
  inferred_type : Type.t;
}

type aexpr_t =
  | Unit of t                               (* Unit literal *)
  | Bool of t                               (* Boolean literal *)
  | Int of t                                (* Integer literal *)
  | Eq of aexpr_t * aexpr_t                 (* Polymorphic equality *)
  | Neq of aexpr_t * aexpr_t                (* Polymorphic inequality *)
  | Leq of aexpr_t * aexpr_t                (* Polymorphic "less than or equal to" *)
  | Geq of aexpr_t * aexpr_t                (* Polymorphic "greater than or equal to" *)
  | Less of aexpr_t * aexpr_t               (* Polymorphic "less than" *)
  | Greater of aexpr_t * aexpr_t            (* Polymorphic "greater than" *)
  | Add of aexpr_t * aexpr_t                (* Integer addition *)
  | Sub of aexpr_t * aexpr_t                (* Integer subtraction *)
  | Mul of aexpr_t * aexpr_t                (* Integer multiplication *)
  | Div of aexpr_t * aexpr_t                (* Integer division *)
  | Mod of aexpr_t * aexpr_t                (* Integer modulus *)
  | Not of aexpr_t                          (* Boolean negation *)
  | Neg of aexpr_t                          (* Integer negation *)
  | If of aexpr_t * aexpr_t * aexpr_t       (* Conditional expression *)
  | Var of t                                (* Variable *)
  | Let of t * (t list) * aexpr_t * aexpr_t (* Let expression *)
  | Apply of aexpr_t * (aexpr_t list)       (* Function application *)


let typevar_count = ref 0

let reset_type_vars () =
  typevar_count := 0

(* Generates a fresh type variable, using the following pattern:
 * a, b, ..., z, a1, a2, ... *)
let make_type_var () : Type.t =
  let num_chars = 26 in
  let string_rep =
    if !typevar_count < num_chars then
      String.make 1 (Char.chr (!typevar_count + (Char.code 'a')))
    else
      "a" ^ (string_of_int (!typevar_count + 1 - num_chars))
  in
  let () = incr typevar_count in
  Type.Var string_rep


(* Generate fresh type-vars for all the variables appearing in a let-binding.
 * 
 * Returns: (f_annot, f_typevar, args_annot, args_typevars) where
 *    f_annot is a variable expression annotated with a fresh type variable
 *    f_typevar is a singleton mapping from f's variable name to the new type var
 *    args_annot is a list of variable expressions annotated with fresh type variables
 *    args_typevars is a mapping from the args' variable names to their new type vars
 *)
let annot_let_vars f args : t * (Type.t SMap.t) * (t list) * (Type.t SMap.t) =
  let annot_var syn = match syn.Syntax.expr with
    | Syntax.Var var_name ->
        let annot = {parsed_expr = syn; inferred_type = make_type_var ()} in
        (annot, SMap.add var_name annot.inferred_type SMap.empty)
    | _ -> assert false
  in
  let (f_annot, f_typevar) = annot_var f in
  let (args_annot, args_typevars) = List.fold_left
    (fun (args_acc, tvars_acc) arg ->
      let (arg_annot, arg_tvar) = annot_var arg in
      (args_acc @ [arg_annot], smap_union_prefer_first arg_tvar tvars_acc))
    ([], SMap.empty)
    args
  in
  (f_annot, f_typevar, args_annot, args_typevars)


(* Recursively annotate all subexpressions with types.
 *    env         : environment in which the expression is evaluated; maps bindings to types
 *    parsed_expr : an untyped expression, as obtained from the parser
 *)
let rec annotate (env : Type.t SMap.t) (parsed_expr : Syntax.t) : aexpr_t =
  match parsed_expr.Syntax.expr with
  | Syntax.Unit           -> Unit {parsed_expr; inferred_type = Type.Unit}
  | Syntax.Bool _         -> Bool {parsed_expr; inferred_type = Type.Bool}
  | Syntax.Int _          -> Int  {parsed_expr; inferred_type = Type.Int}
  | Syntax.Eq (a, b)      -> Eq      (annotate env a, annotate env b)
  | Syntax.Neq (a, b)     -> Neq     (annotate env a, annotate env b)
  | Syntax.Leq (a, b)     -> Leq     (annotate env a, annotate env b)
  | Syntax.Geq (a, b)     -> Geq     (annotate env a, annotate env b)
  | Syntax.Less (a, b)    -> Less    (annotate env a, annotate env b)
  | Syntax.Greater (a, b) -> Greater (annotate env a, annotate env b)
  | Syntax.Add (a, b)     -> Add     (annotate env a, annotate env b)
  | Syntax.Sub (a, b)     -> Sub     (annotate env a, annotate env b)
  | Syntax.Mul (a, b)     -> Mul     (annotate env a, annotate env b)
  | Syntax.Div (a, b)     -> Div     (annotate env a, annotate env b)
  | Syntax.Mod (a, b)     -> Mod     (annotate env a, annotate env b)
  | Syntax.Not a          -> Not     (annotate env a)
  | Syntax.Neg a          -> Neg     (annotate env a)
  | Syntax.If (a, b, c)   -> If      (annotate env a, annotate env b, annotate env c)
  | Syntax.Var var_name ->
      let var_type = match smap_find var_name env with
        | Some known_type -> known_type
        | None            -> make_type_var ()
      in
      Var {parsed_expr; inferred_type = var_type}
  | Syntax.Let (a, args, b, c) ->
      let (a_annot, a_typevar, args_annot, args_typevars) = annot_let_vars a args in
      (* The first element in the list is the newly-bound variable, which is added to
       * the environment of the "in" clause (shadowing any previous binding). *)
      let in_env = smap_union_prefer_first a_typevar env in
      (* All other elements in the list are function arguments, which are added to the
       * environment of the "equals" clause (shadowing any previous binding). *)
      let eq_env = smap_union_prefer_first args_typevars env in
      Let (a_annot, args_annot, annotate eq_env b, annotate in_env c)
  | Syntax.LetRec (a, args, b, c) ->
      let (a_annot, a_typevar, args_annot, args_typevars) = annot_let_vars a args in
      (* The first element in the list is the newly-bound variable, which is added to
       * the environment of the "in" clause (shadowing any previous binding). *)
      let in_env = smap_union_prefer_first a_typevar env in
      (* All other elements in the list are function arguments, which are added to the
       * environment of the "equals" clause (shadowing any previous binding).
       * In this form, 'a' may recur in the "equals" clause, so the type variable
       * for 'a' is added to the eq_env. *)
      let eq_env = smap_union_prefer_first args_typevars in_env in
      Let (a_annot, args_annot, annotate eq_env b, annotate in_env c)
  | Syntax.Apply (a, args) ->
      Apply (annotate env a, List.map (annotate env) args)


