
type constraint_t = {
  (* The type of a constraint: the term on the left must unify with
   * the type on the right.  [error_info] provides the positions from the
   * source file which should be associated with this constraint for
   * the purpose of generating error messages. *)
  left_type  : Type.t;
  right_type : Type.t;
  error_info : Syntax.parser_meta_t
}


type subst_t = {
  type_var : Type.tvar_t;
  subst    : Type.t
}


exception Unification_failure of constraint_t

(* Determines whether or not a typevar occurs within a type definition *)
let rec occurs (tvar : Type.tvar_t) (typ : Type.t) =
  match typ with
  | Type.Unit         -> false
  | Type.Bool         -> false
  | Type.Int          -> false
  | Type.Var a        -> tvar = a
  | Type.Arrow (a, b) -> (occurs tvar a) || (occurs tvar b)


(* Substitutes [repl] for all occurrences of [orig] within a type definition *)
let rec substitute (orig : Type.tvar_t) (repl : Type.t) (typ : Type.t) : Type.t =
  match typ with
  | Type.Unit | Type.Bool | Type.Int ->
      typ
  | Type.Var a ->
      if a = orig then repl else typ
  | Type.Arrow (a, b) ->
     Type.Arrow (substitute orig repl a, substitute orig repl b)


(* Apply a list of substitutions to a type, in order. *)
let apply_substitutions (substs : subst_t list) (x : Type.t) : Type.t =
  List.fold_left
    (fun acc s -> substitute s.type_var s.subst acc)
    x
    substs


(* Unify a single constraint *)
let rec unify_one (constr : constraint_t) : subst_t list =
  Printf.printf "unify_one:\n    %s\n    %s\n"
    (Type.string_of_type constr.left_type)
    (Type.string_of_type constr.right_type);
  match (constr.left_type, constr.right_type) with
  | ((Type.Unit as x), y)
  | ((Type.Bool as x), y)
  | ((Type.Int as x), y)
  | (y, (Type.Unit as x))
  | (y, (Type.Bool as x))
  | (y, (Type.Int as x)) ->
      begin match y with
      | Type.Unit | Type.Bool | Type.Int | Type.Arrow _ ->
          if constr.left_type = constr.right_type then [] else raise (Unification_failure constr)
      | Type.Var a ->
          [{type_var = a; subst = x}]
      end
  | (Type.Var a, (Type.Var b as x)) ->
      if a = b then [] else [{type_var = a; subst = x}]
  | (Type.Var a, (Type.Arrow (b, c) as x)) | ((Type.Arrow (b, c) as x), Type.Var a) ->
      if occurs a x then
        raise (Unification_failure constr)
      else
        [{type_var = a; subst = x}]
  | (Type.Arrow (a, b), Type.Arrow (c, d)) ->
      begin try
        unify [
          {left_type = a; right_type = c; error_info = constr.error_info};
          {left_type = b; right_type = d; error_info = constr.error_info}
        ]
      with Unification_failure _ ->
        (* This will provide a more meaningful error message; the reference to
         * the source file spans the entire arrow expression. *)
        raise (Unification_failure constr)
      end

(* Unify a list of constraints.  The resulting list has the property
 * that type variables appearing on the "left-hand side" of the substitution
 * do not appear on the "right-hand side" of any following substitution.
 * This allows the list of substitutions to be applied in a single
 * left-to-right pass. *)
and unify (constraints : constraint_t list) : subst_t list =
  match constraints with
  | [] ->
      []
  | constr :: tail ->
      let subst_tail = unify tail in
      let subst_head = unify_one {constr with
        left_type  = apply_substitutions subst_tail constr.left_type;
        right_type = apply_substitutions subst_tail constr.right_type;
      } in
      subst_tail @ subst_head


let string_of_subst subst =
  Printf.sprintf "%s  |->  %s"
    (Type.string_of_typevar_index subst.type_var)
    (Type.string_of_type subst.subst)

let print_substitutions (substs : subst_t list) =
  List.iter (fun subst -> Printf.printf "%s\n" (string_of_subst subst)) substs


