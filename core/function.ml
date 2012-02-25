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
 *
 *    * The variable types are annotated with storage policy information, so that
 *      a later pass can insert lifetime management code for reference types.
 *)

open Printf

module VarID = Normal.VarID
module VMap  = Normal.VMap
module VSet  = Normal.VSet
type binary_op_t = Normal.binary_op_t
type unary_op_t  = Normal.unary_op_t
type cond_t      = Normal.cond_t


type storage_t =
  | Value         (* Value type (int, string, known function, etc.) *)
  | Ref           (* Reference type (array, closure, etc.) *)


(* The type of storage policy-annotated variables. *)
module SPVar = struct
  type t = {id : int; storage : storage_t}
  let compare a b = if a.id < b.id then -1 else if a.id > b.id then 1 else 0
  let to_string (x : t)     = sprintf "v%d" x.id
  let to_int_string (x : t) = sprintf "%d" x.id
end

module SPVMap = Map.Make(SPVar)

type var_t = SPVar.t


type t =
  | Unit                                            (* Unit literal *)
  | Int of int                                      (* Integer constant *)
  | BinaryOp of binary_op_t * var_t * var_t         (* Binary integer operation *)
  | UnaryOp of unary_op_t * var_t                   (* Unary integer operation *)
  | Conditional of cond_t * var_t * var_t * t * t   (* Conditional form *)
  | Var of var_t                                    (* Bound variable reference (not a known function) *)
  | KnownFuncVar of var_t                           (* Known function reference *)
  | Let of var_t * t * t                            (* Let binding for a variable *)
  | ApplyKnown of var_t * (var_t list)              (* Application of "known" function *)
  | ApplyUnknown of var_t * (var_t list)            (* Application of an "unknown" function
                                                          (i.e. call to computed address) *)
  | ArrayAlloc of var_t * var_t                     (* Construct a new array (size, init) *)
  | ArraySet of var_t * var_t * var_t               (* Store a ref or value in an array (arr, index, ref) *)
  | ArrayGet of var_t * var_t                       (* Get a ref or value from an array (arr, index) *)


type function_def_t =
  (* Standard function defined in ZML (function args, function body) *)
  | NativeFunc of (var_t list) * t
  (* Function defined in ASM (with ASM identifier, arg count *)
  | ExtFunc of string * int


type function_t = {
  (** Name of the function (will be injected into the assembly to assist in debugging) *)
  f_name : string;
  f_impl : function_def_t
}

type program_t = {
  (* List of known functions, each indexed by a unique variable id *)
  functions   : function_t SPVMap.t;
  (* Function to be invoked as program entry point (with type "unit -> unit") *)
  entry_point : SPVar.t
}


(* Manually map a variable from Normal representation into storage-policy representation *)
let value_var (v : VarID.t) = {SPVar.id = v.VarID.id; SPVar.storage = Value}
let ref_var   (v : VarID.t) = {SPVar.id = v.VarID.id; SPVar.storage = Ref}

(* Use a variable's type information to infer its storage policy *)
let infer_storage (v : VarID.t) =
  match v.VarID.tp with
  | Type.Unit | Type.Bool _ | Type.Int _ ->
      value_var v
  | Type.Arrow _ ->
      (* Any first-class treatment of a function results in a closure reference. *)
      ref_var v
  | Type.Var _ ->
      (* Polymorphic type... *)
      assert false


(* Formatting rules:
 *  - A newline always follows "in", "then", and "else", as well as the true/false
 *    clauses of if/then.
 *  - The bound expression in a Let is indented iff it is another Let or an If.
 *  - The "true" and "false" expressions in an if-then-else are both indented. *)
let rec string_of_expr ?(indent_level=0) ?(chars_per_indent=2) (expr : t) : string =
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
      sprintf "(%s %s %s)"  (SPVar.to_string a) op_s (SPVar.to_string b)
  | UnaryOp (Normal.Neg, a) -> sprintf "(- %s)" (SPVar.to_string a)
  | Conditional (cond, a, b, c, d) ->
      sprintf "%sif %s %s %s then\n%s%s\n%selse\n%s%s"
        (make_indent indent_level)
        (SPVar.to_string a)
        (match cond with Normal.IfEq -> "=" | Normal.IfLess -> "<")
        (SPVar.to_string b)
        (match c with Let _ | Conditional _ -> "" | _ -> (make_indent (indent_level + 1)))
        (string_of_expr ~indent_level:(indent_level + 1) c)
        (make_indent indent_level)
        (match d with Let _ | Conditional _ -> "" | _ -> (make_indent (indent_level + 1)))
        (string_of_expr ~indent_level:(indent_level + 1) d)
  | Var a | KnownFuncVar a ->
      SPVar.to_string a
  | Let (a, b, c) ->
      begin match b with
      | Let _ | Conditional _ ->
          sprintf "%slet %s =\n%s\n%sin\n%s%s"
            (make_indent indent_level)
            (SPVar.to_string a)
            (string_of_expr ~indent_level:(indent_level + 1) b)
            (make_indent indent_level)
            (match c with | Let _ | Conditional _ -> "" | _ -> (make_indent indent_level))
            (string_of_expr ~indent_level c)
      | _ ->
          sprintf "%slet %s = %s in\n%s%s"
            (make_indent indent_level)
            (SPVar.to_string a)
            (string_of_expr ~indent_level b)
            (match c with | Let _ | Conditional _ -> "" | _ -> (make_indent indent_level))
            (string_of_expr ~indent_level c)
      end
  | ApplyKnown (f, args) ->
      sprintf "apply(%s %s)" (SPVar.to_string f) (String.concat " " (List.map SPVar.to_string args))
  | ApplyUnknown (f, args) ->
      sprintf "apply_unk(%s %s)" (SPVar.to_string f) (String.concat " " (List.map SPVar.to_string args))
  | ArrayAlloc (a, b) ->
      sprintf "array_alloc(%s, %s)" (SPVar.to_string a) (SPVar.to_string b)
  | ArraySet (a, b, c) ->
      sprintf "array_set(%s, %s, %s)" (SPVar.to_string a) (SPVar.to_string b) (SPVar.to_string c)
  | ArrayGet (a, b) ->
      sprintf "array_get(%s, %s)" (SPVar.to_string a) (SPVar.to_string b)



let string_of_function id (f : function_t) : string =
  match f.f_impl with
  | NativeFunc (f_args, f_body) ->
    (sprintf "BEGIN FUNCTION (source name: %s) ==> %s : %s =\n"
      f.f_name
      (SPVar.to_string id)
      begin match f_args with
      | [] -> "()"
      | _  -> String.concat " -> " (List.map SPVar.to_string f_args)
      end) ^
    (string_of_expr f_body) ^
    (sprintf "\nEND FUNCTION (source name: %s)" f.f_name)
  | ExtFunc (ext_impl, _) ->
    sprintf "EXTERNAL %s ==> %s\n" f.f_name ext_impl

let string_of_program (a : program_t) =
  let function_strings = SPVMap.fold
    (fun f_id f_def acc -> (string_of_function f_id f_def) :: acc)
    a.functions
    []
  in
  String.concat "\n\n" function_strings


let function_defs = ref SPVMap.empty

let reset_function_defs () =
  function_defs := SPVMap.empty

(* Add a function definition to the list of known functions. *)
let add_function_def (id : SPVar.t) (def : function_t) : unit =
  (* Due to alpha conversion performed in [Normal.normalize], each [id]
   * shall be program-unique. *)
  let () = assert (not (SPVMap.mem id !function_defs)) in
  function_defs := SPVMap.add id def !function_defs



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



(* Construct a closure definition.  The code which defines the function is transformed into code which
 * allocates an array and stores its free variables into the array. *)
let make_closure_def 
  (f_id : VarID.t)                    (* Function identifier *)
  (closure_id : var_t)                (* Identifier to use for the closure array *)
  (free_vars : VSet.t)                (* Set of free variables to close over *)
  (scope_expr : Normal.t)             (* Expression in which the closure will be in scope *)
  (extract_fun : Normal.t -> t)       (* Method for extracting functions from a subexpression *)
    : t =
  (* Prefix the expression with all the array_set operations necessary to init the closure *)
  let (_, expr_with_array_init) = VSet.fold
    (fun free_var (ofs, exp) ->
      let array_set_expr =
        match free_var.VarID.tp with
        | Type.Unit | Type.Bool _ | Type.Int _ ->
            (* The closure array stores reference types; value types must be boxed
             * so they can be stored in the reference array. *)
            let size_id = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
            let box_id  = {SPVar.id = Normal.free_var (); SPVar.storage = Ref} in
            let ofs_id  = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
            Let (size_id, Int 1,
              Let (box_id, ArrayAlloc (size_id, value_var free_var),
                Let (ofs_id, Int ofs,
                  Let ({SPVar.id = Normal.free_var (); SPVar.storage = Value},
                    ArraySet (closure_id, ofs_id, box_id),
                    exp))))
        | Type.Arrow _ ->
            (* Reference types are stored directly in the closure array.  (Note that a
             * function which appears in this context (as a free variable) is an unknown
             * function and is therefore of reference type. *)
            let ofs_id = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
            Let (ofs_id, Int ofs,
              Let ({SPVar.id = Normal.free_var (); SPVar.storage = Value},
                ArraySet (closure_id, ofs_id, ref_var free_var),
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
  let box_size_id      = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
  let known_func_id    = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
  let closure_func_ref = {SPVar.id = Normal.free_var (); SPVar.storage = Ref} in
  let closure_size_id  = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
  Let (box_size_id, Int 1,
    Let (known_func_id, KnownFuncVar (value_var f_id),
      Let (closure_func_ref, ArrayAlloc (box_size_id, known_func_id),
        Let (closure_size_id, Int (1 + (VSet.cardinal free_vars)),
          Let (closure_id, ArrayAlloc (closure_size_id, closure_func_ref),
            expr_with_array_init)))))


(* Construct the body for a function which is invoked using the calling convention for closures. *)
let make_closure_fun_body
  (closure_id : var_t)                  (* Identifier for the closure array *)
  (free_vars : VSet.t)                  (* Variables stored in the closure array *)
  (extract_fun : Normal.t -> t)         (* Method for extracting functions from a subexpression *)
  (body : Normal.t)                     (* Function body to be altered *)
    : t =
  (* Using the naive approach here: systematically unpacking every free variable from the
   * closure array.  This will create a bunch of unnecessary register pressure; a better
   * implementation would unpack free variables closer to time-of-use. *)
  let (_, body_extracted) =
    VSet.fold
      (fun free_var (ofs, exp) ->
        let array_get_expr =
          match free_var.VarID.tp with
          | Type.Unit | Type.Bool _ | Type.Int _ ->
              (* Value types are boxed, so we have to do a double-dereference *)
              let closure_ofs_id = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
              let box_id         = {SPVar.id = Normal.free_var (); SPVar.storage = Ref} in
              let box_ofs_id     = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
              Let (closure_ofs_id, Int ofs,
                Let (box_id, ArrayGet (closure_id, closure_ofs_id),
                  Let (box_ofs_id, Int 0,
                    Let (value_var free_var, ArrayGet (box_id, box_ofs_id),
                      exp))))
          | Type.Arrow _ ->
              (* Reference types are stored directly in the closure array.  (Note that a
               * function which appears in this context (as a free variable) is an unknown
               * function and is therefore of reference type. *)
              let ofs_id = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
              Let (ofs_id, Int ofs,
                Let (ref_var free_var, ArrayGet (closure_id, ofs_id),
                  exp))
          | Type.Var _ ->
              (* Polymorphic free variable? *)
              assert false
        in
        (ofs + 1, array_get_expr))
      free_vars
      (1, extract_fun body)
  in
  body_extracted


(* Insert code to invoke a closure. *)
let make_closure_application closure_id args =
  let closure_ofs_id = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
  let box_id         = {SPVar.id = Normal.free_var (); SPVar.storage = Ref} in
  let box_ofs_id     = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
  let func_id        = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
  Let (closure_ofs_id, Int 0,
    Let (box_id, ArrayGet (closure_id, closure_ofs_id),
      Let (box_ofs_id, Int 0,
        Let (func_id, ArrayGet (box_id, box_ofs_id),
          ApplyUnknown (func_id, closure_id :: args)))))


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
  (callable_ids : call_t VMap.t)  (* Function ids which could be referenced in this expr *)
  (normal_expr : Normal.t)        (* Expression to process *)
    : t =                         (* Resulting expression, with functions extracted *)
  match normal_expr with
  | Normal.Unit                -> Unit
  | Normal.Int x               -> Int x
  | Normal.BinaryOp (op, a, b) -> BinaryOp (op, infer_storage a, infer_storage b)
  | Normal.UnaryOp (op, a)     -> UnaryOp  (op, infer_storage a)
  | Normal.Var a ->
      begin try
        (* If an identifier was closure-converted, here we use a reference to the closure array
         * instead of the converted identifier. *)
        let f = VMap.find a callable_ids in
        match f with
        | Known ->
            KnownFuncVar (value_var a)
        | Closure r ->
            Var r
        with Not_found ->
          Var (infer_storage a)
      end
  | Normal.Conditional (cond, a, b, e1, e2) ->
      Conditional (cond, infer_storage a, infer_storage b, extract_functions_aux callable_ids e1,
        extract_functions_aux callable_ids e2)
  | Normal.Let (a, e1, e2) ->
      Let (infer_storage a, extract_functions_aux callable_ids e1, extract_functions_aux callable_ids e2)
  | Normal.LetFun (f_name, f_id, f_args, f_body, f_scope_expr) ->
      let f_arg_set  = List.fold_left (fun acc x -> VSet.add x acc) VSet.empty f_args in
      let bound_vars = VSet.add f_id (VMap.fold (fun x _ acc -> VSet.add x acc) callable_ids f_arg_set) in
      let free_vars  = free_variables bound_vars f_body in
      if VSet.is_empty free_vars &&
          not (is_first_class f_id f_body) &&
          not (is_first_class f_id f_scope_expr) then
        (* Known-function optimization.  This function is always invoked directly using a full
         * argument set, so we don't need to box it in a closure array. *)
        let callable_ids = VMap.add f_id Known callable_ids in
        let body_extracted = extract_functions_aux callable_ids f_body in
        let () = add_function_def (value_var f_id)
          {f_name; f_impl = NativeFunc (List.map infer_storage f_args, body_extracted)}
        in
        extract_functions_aux callable_ids f_scope_expr
      else
        (* Closure conversion. *)
        let closure_id = {SPVar.id = Normal.free_var (); SPVar.storage = Ref} in
        let callable_ids = VMap.add f_id (Closure closure_id) callable_ids in
        let body_extracted = make_closure_fun_body
          closure_id free_vars (extract_functions_aux callable_ids) f_body
        in
        let () = add_function_def (value_var f_id)
          {f_name; f_impl = NativeFunc (closure_id :: (List.map infer_storage f_args), body_extracted)}
        in
        make_closure_def f_id closure_id free_vars f_scope_expr (extract_functions_aux callable_ids)
  | Normal.External (f_name, f_id, f_ext_impl, f_arg_count, f_scope_expr) ->
      let callable_ids = VMap.add f_id Known callable_ids in
      let () = add_function_def (value_var f_id) {f_name; f_impl = ExtFunc (f_ext_impl, f_arg_count)} in
      extract_functions_aux callable_ids f_scope_expr
  | Normal.Apply (f_id, f_args) ->
      (* FIXME: if the number of args passed does not match the number of args in the function
       * definition, then this expression should reduce to some sort of closure. *)
      let sp_f_args = List.map infer_storage f_args in
      begin try
        match VMap.find f_id callable_ids with
        | Known ->
            ApplyKnown (value_var f_id, sp_f_args)
        | Closure closure_id ->
            make_closure_application closure_id sp_f_args
      with Not_found ->
        (* "Unknown" function application, i.e. call-by-function-pointer. *)
        make_closure_application (ref_var f_id) sp_f_args
      end


(* Rewrite a normalized expression tree as a list of function definitions and an entry point. *)
let extract_functions (expr : Normal.t) : program_t =
  let () = reset_function_defs () in
  let toplevel_expr = extract_functions_aux VMap.empty expr in
  (* Construct the program entry point, [zml_main : unit -> unit] *)
  let main_id = {SPVar.id = Normal.reserved_main_id; SPVar.storage = Value} in
  let () = add_function_def main_id {f_name = "zml_main"; f_impl = NativeFunc ([], toplevel_expr)} in
  {functions = !function_defs; entry_point = main_id}


