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
 *)

open Printf


(* The type of program-unique variable identifiers. *)
module VarID = struct
  type t = int
  let compare e1 e2 = if e1 < e2 then -1 else if e1 > e2 then 1 else 0
  let to_string     (x : t) : string = sprintf "x%d" x
  let to_int_string (x : t) : string = sprintf "%d"  x
end

type var_t = VarID.t

(* Used in module Function. *)
module VMap = Map.Make(VarID)
module VSet = Set.Make(VarID)

(* Used for mapping string variable names to var_t variable ids *)
module SMap = Map.Make(String)


type storage_type_t =
  | Value     (* This variable holds a value (int, string, function address, etc.) *)
  | Ref       (* This variable holds a heap reference (array or list) *)

(* This is a wrapper for variables which captures information about their storage policies. *)
type sp_var_t = {
  storage : storage_type_t;
  var_id  : var_t
}

type t =
  | Unit                                                  (* Unit literal *)
  | Int of int                                            (* Integer constant *)
  | Add of var_t * var_t                                  (* Integer addition *)
  | Sub of var_t * var_t                                  (* Integer subtraction *)
  | Mul of var_t * var_t                                  (* Integer multiplication *)
  | Div of var_t * var_t                                  (* Integer division *)
  | Mod of var_t * var_t                                  (* Integer modulus *)
  | Neg of var_t                                          (* Integer negation *)
  | IfEq of var_t * var_t * t * t                         (* Branching on integer equality test *)
  | IfLess of var_t * var_t * t * t                       (* Branching on integer ordering test *)
  | Var of sp_var_t                                       (* Bound variable *)
  | Let of sp_var_t * t * t                               (* Let binding for a value type *)
  | LetFun of string * var_t * (sp_var_t list) * t * t    (* Let binding for a function definition *)
  | External of string * var_t * string * int * t         (* External function definition *)
  | Apply of var_t * (sp_var_t list)                      (* Function application *)


let rec string_of_normal (ast : t) : string =
  match ast with
  | Unit -> "()"
  | Int i -> string_of_int i
  | Add (a, b) -> sprintf "(%s + %s)"  (VarID.to_string a) (VarID.to_string b)
  | Sub (a, b) -> sprintf "(%s - %s)"  (VarID.to_string a) (VarID.to_string b)
  | Mul (a, b) -> sprintf "(%s * %s)"  (VarID.to_string a) (VarID.to_string b)
  | Div (a, b) -> sprintf "(%s / %s)"  (VarID.to_string a) (VarID.to_string b)
  | Mod (a, b) -> sprintf "(%s %% %s)" (VarID.to_string a) (VarID.to_string b)
  | Neg a -> sprintf "(- %s)\n" (VarID.to_string a)
  | IfEq (a, b, c, d) ->
      sprintf "if %s = %s then\n    %s\nelse\n    %s\n"
      (VarID.to_string a) (VarID.to_string b) (string_of_normal c) (string_of_normal d)
  | IfLess (a, b, c, d) ->
      sprintf "if %s < %s then\n    %s\nelse\n    %s\n"
      (VarID.to_string a) (VarID.to_string b) (string_of_normal c) (string_of_normal d)
  | Var {storage = _; var_id = a} ->
      VarID.to_string a
  | Let ({storage = _; var_id = a}, b, c) ->
      sprintf "let %s = %s in\n%s" (VarID.to_string a) (string_of_normal b) (string_of_normal c)
  | LetFun (name, id, args, def, use) ->
      sprintf "let %s_%s %s = %s in\n%s" name (VarID.to_string id)
        (String.concat " " (List.map (fun x -> VarID.to_string x.var_id) args))
        (string_of_normal def) (string_of_normal use)
  | External (name, id, ext_impl, _, use) ->
      sprintf "external %s_%s = %s in\n%s" name (VarID.to_string id) ext_impl (string_of_normal use)
  | Apply (f, args) ->
      sprintf "apply(%s %s)" (VarID.to_string f)
        (String.concat " " (List.map (fun x -> VarID.to_string x.var_id) args))



(* This type is used to associate string variable names with the program-unique
 * var_t variable identifiers. *)
type rename_context_t = sp_var_t SMap.t

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
let free_named_var renames storage name =
  let x = {storage; var_id = free_var()} in
  (SMap.add name x renames, x)


(* Given an arrow type, compute the number of arguments the function consumes. *)
let rec count_arrow_type_args ?(acc=0) x =
  match x with
  | Type.Arrow (a, b) ->
      count_arrow_type_args ~acc:(acc + 1) b
  | _ ->
      acc


(* Insert a let expression which binds a temporary variable to an intermediate
 * expression. *)
let rec insert_let
  (renames : rename_context_t)      (* Associates string variable names with sp_var_t's *)
  (storage : storage_type_t)        (* Determines the type of storage to associate with the var *)
  (aexpr : Typing.aexpr_t)          (* Expression to be bound *)
  (f : sp_var_t -> t)               (* Constructs an expression which uses the new binding *)
    : t =
  begin match aexpr.Typing.expr with
  | Typing.Var var_name ->
      (* The lookup never fails, because the type checker verified that the variable is bound. *)
      f (SMap.find var_name renames)
  | _ ->
      let new_sp_var = {storage; var_id = free_var ()} in
      let eq_norm = normalize_aux renames aexpr.Typing.expr in
      let in_norm = f new_sp_var in
      Let (new_sp_var, eq_norm, in_norm)
  end

(* Convenience function: insert a pair of let expressions, as required when
 * expanding a binary operation.  The let-expressions will bind to value types. *)
and insert_binary_let_value
  (renames : rename_context_t)
  (a : Typing.aexpr_t)
  (b : Typing.aexpr_t)
  (f : var_t -> var_t -> t)
    : t =
  insert_let renames Value a
    (fun a_binding -> insert_let renames Value b
      (fun b_binding -> f a_binding.var_id b_binding.var_id))

(* Normalize an expression of the form "if a < b then true_val else false_val" *)
and normalize_integer_less renames a b true_val false_val =
  insert_binary_let_value renames a b
    (fun a_binding b_binding -> IfLess (a_binding, b_binding, true_val, false_val))

(* Normalize a "let" or "let rec" expression. *)
and normalize_let
  (renames : rename_context_t)    (* Variable renaming context for the current expression *)
  (is_rec : bool)                 (* true iff this is a "let rec" form *)
  (name : Typing.bind_t)          (* Name of the variable being bound *)
  (args : Typing.bind_t list)     (* Function argument list (possibly empty) *)
  (eq_expr : Typing.aexpr_t)      (* Expression being bound to a variable *)
  (in_expr : Typing.aexpr_t)      (* Expression in which the binding is in scope *)
    : t =
  let (in_renames, binding) =
    match name.Typing.bind_type with
    | Type.Unit | Type.Bool | Type.Int | Type.Arrow (_, _) ->
        free_named_var renames Value name.Typing.bind_name
    | Type.Var _ ->
        (* FIXME: polymorphism? *)
        assert false
  in
  (* Alloc fresh variables for all function arguments *)
  let (eq_renames, arg_vars) = List.fold_left
    (fun (ren, vars) arg ->
      let (ren, new_arg_var) =
        match arg.Typing.bind_type with
        | Type.Unit | Type.Bool | Type.Int | Type.Arrow (_, _) ->
            free_named_var ren Value arg.Typing.bind_name
        | Type.Var _ ->
            (* FIXME: polymorphism? *)
            assert false
      in
      (ren, vars @ [new_arg_var]))
    (* If this is a "let rec" form, then the function name may
     * recur in the "=" expression *)
    ((if is_rec then in_renames else renames), [])
    args
  in
  let eq_norm = normalize_aux eq_renames eq_expr.Typing.expr in
  let in_norm = normalize_aux in_renames in_expr.Typing.expr in
  match args with
  | [] -> Let (binding, eq_norm, in_norm)
  | _  -> LetFun (name.Typing.bind_name, binding.var_id, arg_vars, eq_norm, in_norm)

(* Convert a type-annotated syntax tree into the normalized form. *)
and normalize_aux
  (renames : rename_context_t)      (* Variable renaming context for the current expression *)
  (expr    : Typing.expr_t)         (* Expression to be normalized *)
    : t =
  match expr with
  | Typing.Unit ->
      Unit
  | Typing.Bool a ->
      if a then (Int 1) else (Int 0)
  | Typing.Int n ->
      Int n
  | Typing.Eq (a, b) ->
      insert_binary_let_value renames a b
        (fun a_binding b_binding ->
          match a.Typing.inferred_type with
          | Type.Unit ->
              (* Unit equality never fails *)
              Int 1
          | Type.Bool
          | Type.Int
          | Type.Arrow _ ->
              (* Either an integer value equality test, or a function pointer equality test *)
              IfEq (a_binding, b_binding, Int 1, Int 0)
          | Type.Var _ ->
              (* Type variables shall be eliminated *)
              assert false)
  | Typing.Neq (a, b) ->
      insert_binary_let_value renames a b
        (fun a_binding b_binding ->
          match a.Typing.inferred_type with
          | Type.Unit ->
              (* Unit equality never fails *)
              Int 1
          | Type.Bool
          | Type.Int
          | Type.Arrow _ ->
              (* Either an integer value inequality test, or a function pointer inequality test *)
              IfEq (a_binding, b_binding, Int 0, Int 1)
          | Type.Var _ ->
              (* Type variables shall be eliminated *)
              assert false)
  | Typing.Leq (a, b) ->
      (* a <= b --> not (b < a) *)
      normalize_integer_less renames b a (Int 0) (Int 1)
  | Typing.Geq (a, b) ->
      (* a >= b --> not (a < b) *)
      normalize_integer_less renames a b (Int 0) (Int 1)
  | Typing.Less (a, b) ->
      normalize_integer_less renames a b (Int 1) (Int 0)
  | Typing.Greater (a, b) ->
      (* a > b --> b < a *)
      normalize_integer_less renames b a (Int 1) (Int 0)
  | Typing.Add (a, b) ->
      insert_binary_let_value renames a b
        (fun a_binding b_binding -> Add (a_binding, b_binding))
  | Typing.Sub (a, b) ->
      insert_binary_let_value renames a b
        (fun a_binding b_binding -> Sub (a_binding, b_binding))
  | Typing.Mul (a, b) ->
      insert_binary_let_value renames a b
        (fun a_binding b_binding -> Mul (a_binding, b_binding))
  | Typing.Div (a, b) ->
      insert_binary_let_value renames a b
        (fun a_binding b_binding -> Div (a_binding, b_binding))
  | Typing.Mod (a, b) ->
      insert_binary_let_value renames a b
        (fun a_binding b_binding -> Mod (a_binding, b_binding))
  | Typing.Not a ->
      (* Let the optimizer deal with it... *)
      insert_let renames Value a
        (fun a_binding ->
          let one_binding = {storage = Value; var_id = free_var ()} in
          Let (one_binding, Int 1,
            IfEq (a_binding.var_id, one_binding.var_id, Int 0, Int 1)))
  | Typing.Neg a ->
      insert_let renames Value a
        (fun a_binding -> Neg a_binding.var_id)
  | Typing.If ({Typing.expr = Typing.Eq (a, b); _}, true_expr, false_expr) ->
      let true_norm  = normalize_aux renames true_expr.Typing.expr in
      let false_norm = normalize_aux renames false_expr.Typing.expr in
      insert_binary_let_value renames a b
        (fun a_binding b_binding ->
          match a.Typing.inferred_type with
          | Type.Unit ->
              (* Unit equality never fails *)
              true_norm
          | Type.Bool
          | Type.Int
          | Type.Arrow _ ->
              (* Either an integer value equality test, or a function pointer equality test *)
              IfEq (a_binding, b_binding, true_norm, false_norm)
          | Type.Var _ ->
              (* Type variables shall be eliminated *)
              assert false)
  | Typing.If ({Typing.expr = Typing.Neq (a, b); _}, true_expr, false_expr) ->
      let true_norm  = normalize_aux renames true_expr.Typing.expr in
      let false_norm = normalize_aux renames false_expr.Typing.expr in
      insert_binary_let_value renames a b
        (fun a_binding b_binding ->
          match a.Typing.inferred_type with
          | Type.Unit ->
              (* Unit inequality always fails *)
              false_norm
          | Type.Bool
          | Type.Int
          | Type.Arrow _ ->
              (* Either an integer value inequality test, or a function pointer inequality test *)
              IfEq (a_binding, b_binding, false_norm, true_norm)
          | Type.Var _ ->
              (* Type variables shall be eliminated *)
              assert false)
  | Typing.If ({Typing.expr = Typing.Leq (a, b); _}, true_expr, false_expr) ->
      let true_norm  = normalize_aux renames true_expr.Typing.expr in
      let false_norm = normalize_aux renames false_expr.Typing.expr in
      (* a <= b --> not (b < a) *)
      normalize_integer_less renames b a false_norm true_norm
  | Typing.If ({Typing.expr = Typing.Geq (a, b); _}, true_expr, false_expr) ->
      let true_norm  = normalize_aux renames true_expr.Typing.expr in
      let false_norm = normalize_aux renames false_expr.Typing.expr in
      (* a >= b --> not (a < b) *)
      normalize_integer_less renames a b false_norm true_norm
  | Typing.If ({Typing.expr = Typing.Less (a, b); _}, true_expr, false_expr) ->
      let true_norm  = normalize_aux renames true_expr.Typing.expr in
      let false_norm = normalize_aux renames false_expr.Typing.expr in
      normalize_integer_less renames a b true_norm false_norm
  | Typing.If ({Typing.expr = Typing.Greater (a, b); _}, true_expr, false_expr) ->
      let true_norm  = normalize_aux renames true_expr.Typing.expr in
      let false_norm = normalize_aux renames false_expr.Typing.expr in
      (* a > b --> b < a *)
      normalize_integer_less renames b a true_norm false_norm
  | Typing.If (cond, true_expr, false_expr) ->
      let true_norm  = normalize_aux renames true_expr.Typing.expr in
      let false_norm = normalize_aux renames false_expr.Typing.expr in
      insert_let renames Value cond
        (fun cond_binding ->
          let one_binding = {storage = Value; var_id = free_var ()} in
          Let (one_binding, Int 1,
            IfEq (cond_binding.var_id, one_binding.var_id, true_norm, false_norm)))
  | Typing.Var var_name ->
      (* If this lookup fails, then the variable is unbound.  This shouldn't happen,
       * as the type-checker would have caught it. *)
      Var (SMap.find var_name renames)
  | Typing.Let (name, args, eq_expr, in_expr) ->
      normalize_let renames false name args eq_expr in_expr
  | Typing.LetRec (name, args, eq_expr, in_expr) ->
      normalize_let renames true name args eq_expr in_expr
  | Typing.External (name, ext_impl, in_expr) ->
      let arg_count = count_arrow_type_args name.Typing.bind_type in
      let () = assert (arg_count > 0) in
      let (in_renames, binding) = free_named_var renames Value name.Typing.bind_name in
      let in_norm = normalize_aux in_renames in_expr.Typing.expr in
      External (name.Typing.bind_name, binding.var_id, ext_impl, arg_count, in_norm)
  | Typing.Apply (fun_expr, fun_args) ->
      (* The function arguments are, in general, entire expression trees.  So wrap
       * each argument in a let-binding. *)
      let arg_bindings = List.map
        (fun aexpr ->
          match aexpr.Typing.expr with
          | Typing.Var var_name ->
              (* No let-binding required; argument already has simple variable form *)
              (SMap.find var_name renames, None)
          | _ ->
              let storage =
                match aexpr.Typing.inferred_type with
                | Type.Unit | Type.Bool | Type.Int _ | Type.Arrow (_, _) ->
                    Value
                | Type.Var _ ->
                    (* FIXME: polymorphic type? *)
                    assert false
              in
              ({storage; var_id = free_var ()}, Some (normalize_aux renames aexpr.Typing.expr)))
        fun_args
      in
      let arg_ids = List.map fst arg_bindings in
      List.fold_right
        (fun (arg_var, arg_norm_opt) acc ->
          match arg_norm_opt with
          | Some arg_norm -> Let (arg_var, arg_norm, acc)
          | None          -> acc)
        arg_bindings
        (insert_let renames Value fun_expr
          (fun fun_binding -> Apply (fun_binding.var_id, arg_ids)))


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
  | IfEq (a, b, c, d) ->
      IfEq (a, b, flatten c, flatten d)
  | IfLess (a, b, c, d) ->
      IfLess (a, b, flatten c, flatten d)
  | LetFun (x_name, x, args, body, use) ->
      LetFun (x_name, x, args, flatten body, flatten use)
  | e -> e


(* Convert a type-annotated syntax tree into the normalized form. *)
let normalize (aexpr : Typing.aexpr_t) : t =
  let () = reset_vars () in
  flatten (normalize_aux SMap.empty aexpr.Typing.expr)

