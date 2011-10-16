(* Implementation of type inference, roughly following Algorithm W of
 * Damas and Milner. *)


module SMap = Map.Make(String)
module SSet = Set.Make(String)


(* Exceptionless variant of Map.find. *)
let smap_find x m =
  try Some (SMap.find x m)
  with Not_found -> None


type t =
  | Unit                                              (* Unit literal *)
  | Bool of bool                                      (* Boolean literal *)
  | Int of int                                        (* Integer literal *)
  | Eq of aexpr_t * aexpr_t                           (* Polymorphic equality *)
  | Neq of aexpr_t * aexpr_t                          (* Polymorphic inequality *)
  | Leq of aexpr_t * aexpr_t                          (* Polymorphic "less than or equal to" *)
  | Geq of aexpr_t * aexpr_t                          (* Polymorphic "greater than or equal to" *)
  | Less of aexpr_t * aexpr_t                         (* Polymorphic "less than" *)
  | Greater of aexpr_t * aexpr_t                      (* Polymorphic "greater than" *)
  | Add of aexpr_t * aexpr_t                          (* Integer addition *)
  | Sub of aexpr_t * aexpr_t                          (* Integer subtraction *)
  | Mul of aexpr_t * aexpr_t                          (* Integer multiplication *)
  | Div of aexpr_t * aexpr_t                          (* Integer division *)
  | Mod of aexpr_t * aexpr_t                          (* Integer modulus *)
  | Not of aexpr_t                                    (* Boolean negation *)
  | Neg of aexpr_t                                    (* Integer negation *)
  | If of aexpr_t * aexpr_t * aexpr_t                 (* Conditional expression *)
  | Var of string                                     (* Bound variable *)
  | Let of bind_t * (bind_t list) * aexpr_t * aexpr_t (* Let expression *)
  | Apply of aexpr_t * (aexpr_t list)                 (* Function application *)

and aexpr_t = {
  expr          : t;                     (* Expression *)
  inferred_type : Type.t;                (* Inferred type of expression (possibly a typevar) *)
  parser_info   : Syntax.parser_meta_t   (* Additional info from parser regarding this expr *)
}

and bind_t = {
  bind_name : string;
  bind_type : Type.t
}


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
      Printf.sprintf "a%d" (!typevar_count + 1 - num_chars)
  in
  let () = incr typevar_count in
  Type.Var string_rep


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
      inferred_type = make_type_var ();
      parser_info
    }
  | Syntax.Var var_name ->
      let var_type = match smap_find var_name env with
        | Some known_type -> known_type
        | None            -> make_type_var ()
      in {
        expr          = Var var_name;
        inferred_type = var_type;
        parser_info
      }
  | Syntax.Let (a, args, b, c) -> {
      expr          = annotate_let false env a args b c;
      inferred_type = make_type_var ();
      parser_info
    }
  | Syntax.LetRec (a, args, b, c) -> {
      expr = annotate_let true env a args b c;
      inferred_type = make_type_var ();
      parser_info
    }
  | Syntax.Apply (a, args) -> {
      expr          = Apply (annotate env a, List.map (annotate env) args);
      inferred_type = make_type_var ();
      parser_info
    }


(* Annotate a let-binding with type variables. *) 
and annotate_let is_rec env binding args eq_expr in_expr =
  (* The first element in the list is the newly-bound variable, which is added to
   * the environment of the "in" clause (shadowing any previous binding). *)
  let fun_binding = {bind_name = binding; bind_type = make_type_var () } in
  let in_env = SMap.add fun_binding.bind_name fun_binding.bind_type env in
  (* If this is a "let rec" form, then the binding may recur in the "equals"
   * clause, so the binding must be added to the eq_env. *)
  let env = if is_rec then in_env else env in
  (* All other elements in the list are function arguments, which are added to the
   * environment of the "equals" clause (shadowing any previous binding). *)
  let arg_bindings = List.map
    (fun arg_name -> {bind_name = arg_name; bind_type = make_type_var ()})
    args
  in
  let eq_env = List.fold_left
    (fun env_acc arg_binding -> SMap.add arg_binding.bind_name arg_binding.bind_type env_acc)
    env
    arg_bindings
  in 
  Let (fun_binding, arg_bindings, annotate eq_env eq_expr, annotate in_env in_expr)



type constraint_t = {
  (* The type of a constraint: the term on the left must unify with
   * the type on the right.  [error_info] provides the positions from the
   * source file which should be associated with this constraint for
   * the purpose of generating error messages. *)
  left_type  : Type.t;
  right_type : Type.t;
  error_info : Syntax.parser_meta_t
}


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
        error_info = b.parser_info
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
  | {expr = Let (fun_binding, arg_bindings, eq_expr, in_expr); _} as ae :: tail ->
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

