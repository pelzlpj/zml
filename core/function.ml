(* Implementation of functions and closures.
 *
 *    * Function definitions, represented by Normal.LetFun instances, are lifted
 *      out of the expression tree into a flat list of "toplevel" objects.
 *
 *    * Function invocations, represented by Normal.Apply instances, are
 *      transformed into direct calls of known functions (when possible)
 *      or runtime dispatch to closures (in general).
 *
 *    * The program representation is transformed from an expression tree into a
 *      list of function definitions along with an entry point.
 *)

open Printf

module VarID = Normal.VarID
module VMap  = Normal.VMap
module VSet  = Normal.VSet
type var_t         = Normal.var_t
type binary_op_t   = Normal.binary_op_t
type unary_op_t    = Normal.unary_op_t
type conditional_t = Normal.conditional_t


type expr_t =
  | Unit                                      (* Unit literal *)
  | Int of int                                (* Integer constant *)
  | BinaryOp of binary_op_t * var_t * var_t   (* Binary integer operation *)
  | UnaryOp of unary_op_t * var_t             (* Unary integer operation *)
  | Conditional of conditional_t * var_t * var_t * expr_t * expr_t
                                              (* Conditional form *)
  | Var of var_t                              (* Bound variable reference *)
  | Let of var_t * expr_t * expr_t            (* Let binding for a value type *)
  | ApplyKnown of var_t * (var_t list)        (* Application of "known" function *)
  | ApplyClosure of var_t * (var_t list)      (* Application of closure (or "unknown" function) *)
  | RefArrayAlloc of var_t * var_t            (* Construct an array for storage of ref types *)
  | ValArrayAlloc of var_t * var_t            (* Construct an array for storage of value types *)
  | RefArraySet of var_t * var_t * var_t      (* Store a reference in a ref array (arr, index, ref) *)
  | ValArraySet of var_t * var_t * var_t      (* Store a value in a value array (arr, index, val) *)
  | RefArrayGet of var_t * var_t              (* Get a reference from a ref array *)
  | ValArrayGet of var_t * var_t              (* Get a value from a value array *)


(* FIXME: might want to drop the types on these args... *)
type function_def_t =
  (* Standard function defined in ZML (function args, function body) *)
  | NativeFunc of (var_t list) * expr_t
  (* Closure defined in ZML (free variable ref array, function args, function body) *)
  | NativeClosure of var_t * (var_t list) * expr_t
  (* Function defined in ASM (with ASM identifier, arg count *)
  | ExtFunc of string * int


type function_t = {
  (** Name of the function (will be injected into the assembly to assist in debugging) *)
  f_name : string;
  f_impl : function_def_t
}

type t = {
  (* List of known functions, each indexed by a unique variable id *)
  functions   : function_t VMap.t;
  (* Function to be invoked as program entry point (with type "unit -> unit") *)
  entry_point : var_t
}


(* Formatting rules:
 *  - A newline always follows "in", "then", and "else", as well as the true/false
 *    clauses of if/then.
 *  - The bound expression in a Let is indented iff it is another Let or an If.
 *  - The "true" and "false" expressions in an if-then-else are both indented. *)
let rec string_of_expr ?(indent_level=0) ?(chars_per_indent=2) (expr : expr_t) : string =
  let make_indent level = String.make (level * chars_per_indent) ' ' in
  match expr with
  | Unit -> "()"
  | Int i -> string_of_int i
  | BinaryOp (op, a, b) ->
      let op_s =
        match op with
        | Normal.Add -> "+"
        | Normal.Sub -> "-"
        | Normal.Mul -> "*"
        | Normal.Div -> "/"
        | Normal.Mod -> "%"
      in
      sprintf "(%s %s %s)"  (VarID.to_string a) op_s (VarID.to_string b)
  | UnaryOp (Normal.Neg, a) -> sprintf "(- %s)" (VarID.to_string a)
  | Conditional (cond, a, b, c, d) ->
      sprintf "%sif %s %s %s then\n%s%s\n%selse\n%s%s"
        (make_indent indent_level)
        (VarID.to_string a)
        (match cond with Normal.IfEq -> "=" | Normal.IfLess -> "<")
        (VarID.to_string b)
        (match c with Let _ | Conditional _ -> "" | _ -> (make_indent (indent_level + 1)))
        (string_of_expr ~indent_level:(indent_level + 1) c)
        (make_indent indent_level)
        (match d with Let _ | Conditional _ -> "" | _ -> (make_indent (indent_level + 1)))
        (string_of_expr ~indent_level:(indent_level + 1) d)
  | Var a ->
      VarID.to_string a
  | Let (a, b, c) ->
      begin match b with
      | Let _ | Conditional _ ->
          sprintf "%slet %s =\n%s\n%sin\n%s%s"
            (make_indent indent_level)
            (VarID.to_string a)
            (string_of_expr ~indent_level:(indent_level + 1) b)
            (make_indent indent_level)
            (match c with | Let _ | Conditional _ -> "" | _ -> (make_indent indent_level))
            (string_of_expr ~indent_level c)
      | _ ->
          sprintf "%slet %s = %s in\n%s%s"
            (make_indent indent_level)
            (VarID.to_string a)
            (string_of_expr ~indent_level b)
            (match c with | Let _ | Conditional _ -> "" | _ -> (make_indent indent_level))
            (string_of_expr ~indent_level c)
      end
  | ApplyKnown (f, args) ->
      sprintf "apply(%s %s)" (VarID.to_string f) (String.concat " " (List.map VarID.to_string args))
  | ApplyClosure (f, args) ->
      sprintf "apply_cls(%s %s)" (VarID.to_string f) (String.concat " " (List.map VarID.to_string args))
  | RefArrayAlloc (a, b) ->
      sprintf "ref_array_alloc(%s, %s)" (VarID.to_string a) (VarID.to_string b)
  | ValArrayAlloc (a, b) ->
      sprintf "val_array_alloc(%s, %s)" (VarID.to_string a) (VarID.to_string b)
  | RefArraySet (a, b, c) ->
      sprintf "ref_array_set(%s, %s, %s)" (VarID.to_string a) (VarID.to_string b) (VarID.to_string c)
  | ValArraySet (a, b, c) ->
      sprintf "val_array_set(%s, %s, %s)" (VarID.to_string a) (VarID.to_string b) (VarID.to_string c)
  | RefArrayGet (a, b) ->
      sprintf "ref_array_get(%s, %s)" (VarID.to_string a) (VarID.to_string b)
  | ValArrayGet (a, b) ->
      sprintf "val_array_get(%s, %s)" (VarID.to_string a) (VarID.to_string b)



let string_of_function id (f : function_t) : string =
  match f.f_impl with
  | NativeFunc (f_args, f_body) ->
    (sprintf "BEGIN FUNCTION (source name: %s) ==> %s : %s =\n"
      f.f_name
      (VarID.to_string id)
      begin match f_args with
      | [] -> "()"
      | _  -> String.concat " -> " (List.map (fun x -> VarID.to_string x) f_args)
      end) ^
    (string_of_expr f_body) ^
    (sprintf "\nEND FUNCTION (source name: %s)" f.f_name)
  | NativeClosure (free_vars_array, f_args, f_body) ->
    (sprintf "BEGIN CLOSURE (source name: %s) ==> %s : %s =\n"
      f.f_name
      (VarID.to_string id)
      begin match f_args with
      | [] -> "()"
      | _  -> String.concat " -> " (List.map (fun x -> VarID.to_string x) f_args)
      end) ^
    (string_of_expr f_body) ^
    (sprintf "\nEND CLOSURE (source name: %s)" f.f_name)
  | ExtFunc (ext_impl, _) ->
    sprintf "EXTERNAL %s ==> %s\n" f.f_name ext_impl

let to_string (a : t) =
  let function_strings = VMap.fold
    (fun f_id f_def acc -> (string_of_function f_id f_def) :: acc)
    a.functions
    []
  in
  String.concat "\n\n" function_strings


let function_defs = ref VMap.empty

let reset_function_defs () =
  function_defs := VMap.empty

(* Add a function definition to the list of known functions. *)
let add_function_def (id : var_t) (def : function_t) : unit =
  (* Due to alpha conversion performed in [Normal.normalize], each [id]
   * shall be program-unique. *)
  let () = assert (not (VMap.mem id !function_defs)) in
  function_defs := VMap.add id def !function_defs



(* Compute the set of all free variables found in an expression. *)
let rec free_variables ?(acc=VSet.empty) (bound_vars : VSet.t) (expr : Normal.t) : VSet.t =
  let accum_free vars =
    List.fold_left
      (fun acc x -> if VSet.mem x bound_vars then acc else VSet.add x acc)
      acc
      vars
  in
  match expr with
  | Normal.Unit | Normal.Int _ | Normal.External _ ->
      acc
  | Normal.BinaryOp (_, a, b) ->
      accum_free [a; b]
  | Normal.UnaryOp (_, a) ->
      accum_free [a]
  | Normal.Var a ->
      accum_free [a]
  | Normal.Conditional (_, a, b, e1, e2) ->
      let e1_free = free_variables ~acc bound_vars e1 in
      let e2_free = free_variables ~acc bound_vars e2 in
      let e1_e2_free = VSet.union e1_free e2_free in
      VSet.union e1_e2_free (accum_free [a; b])
  | Normal.Let (a, e1, e2) ->
      let e1_free = free_variables ~acc bound_vars e1 in
      let e2_free = free_variables ~acc (VSet.add a bound_vars) e2 in
      VSet.union e1_free e2_free
  | Normal.LetFun (_, g, g_args, g_body, g_scope_expr) ->
      (* LetFun is a recursive form, so [g] is bound in its body. *)
      let g_bound_vars = List.fold_left
        (fun acc x -> VSet.add x acc)
        bound_vars
        g_args
      in
      let g_body_free  = free_variables ~acc (VSet.add g g_bound_vars) g_body in
      let g_scope_free = free_variables ~acc (VSet.add g bound_vars) g_scope_expr in
      VSet.union g_body_free g_scope_free
  | Normal.Apply (g, g_args) ->
      accum_free (g :: g_args)



(*
(* Insert RefRelease calls to clean up the list of [refs] before evaluating the [expr]. *)
let rec insert_refs_release refs expr =
  match refs with
  | []          -> expr
  | ref :: tail -> Let (Normal.free_var (), RefRelease ref, insert_refs_release tail expr)
*)


(* Rewrite first-class occurrences of [f_id] so they become occurrences of [h_id]. *)
let rec replace_fun_id f_id h_id (expr : Normal.t) : Normal.t =
  let rewrite e = replace_fun_id f_id h_id e in
  let sub x = if x = f_id then h_id else x in
  match expr with
  | Normal.Unit | Normal.Int _ | Normal.BinaryOp _ | Normal.UnaryOp _ ->
      expr
  | Normal.Conditional (cond, a, b, e1, e2) ->
      Normal.Conditional (cond, a, b, rewrite e1, rewrite e2)
  | Normal.Var a ->
      Normal.Var (sub a)
  | Normal.Let (a, e1, e2) ->
      Normal.Let (a, rewrite e1, rewrite e2)
  | Normal.LetFun (g_name, g_id, g_args, g_body, g_scope_expr) ->
      Normal.LetFun (g_name, g_id, g_args, rewrite g_body, rewrite g_scope_expr)
  | Normal.External (g_name, g_id, g_asm_name, g_arg_count, g_scope_expr) ->
      Normal.External (g_name, g_id, g_asm_name, g_arg_count, rewrite g_scope_expr)
  | Normal.Apply (g_id, g_args) ->
      (* Note: if [g_id] = [f_id], that's not considered a "first-class" occurrence and does not
       * need to be rewritten.  [extract_functions_aux] will detect that a closure is being invoked
       * if it finds [g_id] in the [function_defs] map. *)
      Normal.Apply (g_id, List.map sub g_args)


(* Construct a closure.  The code which defines the function is transformed into code which
 * allocates an array and stores its free variables into the array. *)
let make_closure 
  (f_id : var_t)                      (* Function identifier *)
  (closure_id : var_t)                (* Identifier to use for the closure array *)
  (free_vars : VSet.t)                (* Set of free variables to close over *)
  (scope_expr : Normal.t)             (* Expression in which the closure will be in scope *)
  (extract_fun : Normal.t -> expr_t)  (* Method for extracting functions from a subexpression *)
    : expr_t =
  (* Rewrite the scope_expr so it refers to the closure_id instead of f_id *)
  let scope_expr = replace_fun_id f_id closure_id scope_expr in
  (* Prefix the expression with all the array_set operations necessary to init the closure *)
  let (_, expr_with_array_init) = VSet.fold
    (fun x (ofs, exp) ->
      let array_set_expr =
        match x.VarID.tp with
        | Type.Unit | Type.Bool _ | Type.Int _ ->
            (* Value types are boxed so they can be stored in a reference array. *)
            let size_id = {VarID.id = Normal.free_var (); VarID.tp = Type.Int} in
            let box_id  = {VarID.id = Normal.free_var (); VarID.tp = Type.Unit (* FIXME *)} in
            let ofs_id  = {VarID.id = Normal.free_var (); VarID.tp = Type.Int} in
            Let (size_id, Int 1,
              Let (box_id, ValArrayAlloc (size_id, x),
                Let (ofs_id, Int ofs,
                  Let ({VarID.id = Normal.free_var (); VarID.tp = Type.Unit},
                    RefArraySet (closure_id, ofs_id, box_id),
                    exp))))
        | Type.Arrow _ ->
            (* Reference types are stored directly in the closure array.  (Note that a
             * function which appears in this context (as a free variable) is an unknown
             * function and is therefore of reference type. *)
            let ofs_id = {VarID.id = Normal.free_var (); VarID.tp = Type.Int} in
            Let (ofs_id, Int ofs,
              Let ({VarID.id = Normal.free_var (); VarID.tp = Type.Unit},
                RefArraySet (closure_id, ofs_id, x),
                exp))
        | Type.Var _ ->
            (* Polymorphic free variable? *)
            assert false
      in
      (ofs + 1, array_set_expr))
    free_vars
    (1, extract_fun scope_expr)
  in
  (* Now prepend the closure array allocation.  Note that array location zero holds the closure
   * function itself (boxed), so that the entire closure can be passed around as a first-class
   * value. *)
  let closure_func_ref = {VarID.id = Normal.free_var (); VarID.tp = Type.Unit (* FIXME *)} in
  let box_size_id      = {VarID.id = Normal.free_var (); VarID.tp = Type.Int} in
  let closure_size_id  = {VarID.id = Normal.free_var (); VarID.tp = Type.Int} in
  Let (box_size_id, Int 1,
    Let (closure_func_ref, ValArrayAlloc (box_size_id, f_id),
      Let (closure_size_id, Int (1 + (VSet.cardinal free_vars)),
        Let (closure_id, RefArrayAlloc (closure_size_id, closure_func_ref),
          expr_with_array_init))))



(* Determines whether or not the function with the given [f_id] is ever treated as a first-class
 * citizen within the given [expr]--in other words, whether it is ever used in any way other than
 * simply calling it with a full argument list. *)
let rec is_first_class f_id (expr : Normal.t) : bool =
  match expr with
  | Normal.Unit | Normal.Int _ | Normal.BinaryOp _ | Normal.UnaryOp _ ->
      false
  | Normal.Conditional (cond, a, b, e1, e2) ->
      (is_first_class f_id e1) || (is_first_class f_id e2)
  | Normal.Var x ->
      x = f_id
  | Normal.Let (a, e1, e2) ->
      (is_first_class f_id e1) || (is_first_class f_id e2)
  | Normal.LetFun (g_name, g_id, g_args, g_body, g_scope_expr) ->
      (is_first_class f_id g_body) || (is_first_class f_id g_scope_expr)
  | Normal.External (_, _, _, _, e) ->
      is_first_class f_id e
  | Normal.Apply (g_id, g_args) ->
      (* If [f_id] is passed as a function argument to [g], we will assume that [f_id] must be
       * treated as first-class.  (In some cases higher-order functions could unbox the function
       * argument, but that optimization would require a lot of extra analysis to figure out the
       * contexts in which the higher-order function is invoked.) *)
      List.mem f_id g_args


type call_t = Known | Closure of var_t

(* Extract function bodies from the expression tree, storing them in the [function_defs] map. *)
let rec extract_functions_aux
  (recur_ids : call_t VMap.t) (* Function ids which could be referenced recursively in this expr *)
  (normal_expr : Normal.t)    (* Expression to process *)
    : expr_t =                (* Resulting expression, with functions extracted *)
  match normal_expr with
  | Normal.Unit                -> Unit
  | Normal.Int x               -> Int x
  | Normal.BinaryOp (op, a, b) -> BinaryOp (op, a, b)
  | Normal.UnaryOp  (op, a)    -> UnaryOp  (op, a)
  | Normal.Var a               -> Var a
  | Normal.Conditional (cond, a, b, e1, e2) ->
      Conditional (cond, a, b, extract_functions_aux recur_ids e1,
        extract_functions_aux recur_ids e2)
  | Normal.Let (a, e1, e2) ->
      Let (a, extract_functions_aux recur_ids e1, extract_functions_aux recur_ids e2)
  | Normal.LetFun (f_name, f_id, f_args, f_body, f_scope_expr) ->
      let f_arg_set  = List.fold_left (fun acc x -> VSet.add x acc) VSet.empty f_args in
      let bound_vars = VSet.add f_id (VMap.fold (fun x _ acc -> VSet.add x acc) recur_ids f_arg_set) in
      let free_vars  = free_variables bound_vars f_body in
      if VSet.is_empty free_vars &&
          not (is_first_class f_id f_body) &&
          not (is_first_class f_id f_scope_expr) then
        (* Known-function optimization.  This function is always invoked directly using a full
         * argument set, so we don't need to box it in a closure array. *)
        let body_extracted = extract_functions_aux (VMap.add f_id Known recur_ids) f_body in
        let () = add_function_def f_id {f_name; f_impl = NativeFunc (f_args, body_extracted)} in
        extract_functions_aux recur_ids f_scope_expr
      else
        (* Closure conversion. *)
        (* FIXME: type system is not yet capable of expressing the closure array type, and won't
         * be able to do so until record/tuple product types are integrated.  At this point in time,
         * I don't think we actually need the type to be correct. *)
        let closure_id = {VarID.id = Normal.free_var (); VarID.tp = Type.Unit} in
        let body_extracted = extract_functions_aux (VMap.add f_id (Closure closure_id) recur_ids) f_body in
        let () = add_function_def f_id {f_name; f_impl = NativeClosure (closure_id, f_args, body_extracted)} in
        make_closure f_id closure_id free_vars f_scope_expr (extract_functions_aux recur_ids)
  | Normal.External (f_name, f_id, f_ext_impl, f_arg_count, f_scope_expr) ->
      let () = add_function_def f_id {f_name; f_impl = ExtFunc (f_ext_impl, f_arg_count)} in
      extract_functions_aux recur_ids f_scope_expr
  | Normal.Apply (f_id, f_args) ->
      begin try
        begin match (VMap.find f_id !function_defs).f_impl with
        | NativeFunc _ | ExtFunc _ ->
            ApplyKnown (f_id, f_args)
        | NativeClosure (closure_id, closure_args, _) ->
            ApplyClosure (closure_id, f_args)
        end
      with Not_found ->
        begin try
          (* We hit this case for recursive invocations, as the function application occurs
           * before the function definition has been fully lifted into [function_defs]. *)
          begin match VMap.find f_id recur_ids with
          | Known ->
              ApplyKnown (f_id, f_args)
          | Closure closure_id ->
              ApplyClosure (closure_id, f_args)
          end
        with Not_found ->
          (* "Unknown" function application, i.e. call-by-function-pointer. *)
          ApplyClosure (f_id, f_args)
        end
      end



(* Rewrite a normalized expression tree as a list of function definitions and an entry point. *)
let extract_functions (expr : Normal.t) : t =
  let () = reset_function_defs () in
  let toplevel_expr = extract_functions_aux VMap.empty expr in
  (* Construct the program entry point, [zml_main : unit -> unit] *)
  let main_id = {VarID.id = Normal.reserved_main_id; VarID.tp = Type.Arrow (Type.Unit, Type.Unit)} in
  let () = add_function_def main_id {f_name = "zml_main"; f_impl = NativeFunc ([], toplevel_expr)} in
  {functions = !function_defs; entry_point = main_id}


