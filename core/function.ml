(* Implementation of functions and closures.
 *
 *    * Function definitions, represented by Normal.LetFun instances, are lifted
 *      out of the expression tree into a flat list of "toplevel" objects.
 *
 *    * Function invocations, represented by Normal.Apply instances, are
 *      transformed into direct calls of known functions (when possible)
 *      or runtime dispatch to unknown functions (in general).
 *
 *    * The program representation is transformed from an expression tree into a
 *      list of function definitions along with an entry point.
 *)

open Printf

module VarID  = Normal.VarID
module VMap   = Normal.VMap
module VSet   = Normal.VSet
type var_t    = Normal.var_t
type sp_var_t = Normal.sp_var_t


module SPVarID = struct
  type t      = sp_var_t
  let compare = Pervasives.compare
end

module SPVSet = Set.Make(SPVarID)


type expr_t =
  | Unit                                      (* Unit literal *)
  | Int of int                                (* Integer constant *)
  | Add of var_t * var_t                      (* Integer addition *)
  | Sub of var_t * var_t                      (* Integer subtraction *)
  | Mul of var_t * var_t                      (* Integer multiplication *)
  | Div of var_t * var_t                      (* Integer division *)
  | Mod of var_t * var_t                      (* Integer modulus *)
  | Neg of var_t                              (* Integer negation *)
  | IfEq of var_t * var_t * expr_t * expr_t   (* Branching on integer equality test *)
  | IfLess of var_t * var_t * expr_t * expr_t (* Branching on integer ordering test *)
  | Var of var_t                              (* Bound variable *)
  | Let of var_t * expr_t * expr_t            (* Let binding for a value type *)
  | ApplyKnown of var_t * (var_t list)        (* Application of known function *)
  | ApplyUnknown of var_t * (var_t list)      (* Application of unknown function *)
  | RefArrayAlloc of int * var_t              (* Construct an array for storage of ref types *)
  | ValArrayAlloc of int * var_t              (* Construct an array for storage of value types *)
  | RefClone of var_t                         (* Create a new reference to a heap structure. *)
  | RefRelease of var_t                       (* Drop ownership of a reference *)
  | RefArraySet of var_t * var_t * var_t      (* Store a reference in a ref array (arr, index, ref) *)
  | ValArraySet of var_t * var_t * var_t      (* Store a value in a value array (arr, index, val) *)
  | RefArrayGet of var_t * var_t              (* Get a reference from a ref array *)
  | ValArrayGet of var_t * var_t              (* Get a value from a value array *)


(* FIXME: might want to drop the types on these args... *)
type function_def_t =
  (* Standard function defined in ZML (function args, function body) *)
  | NativeFunc of (sp_var_t list) * expr_t
  (* Closure defined in ZML (free variable ref array, function args, function body) *)
  | NativeClosure of var_t * (sp_var_t list) * expr_t
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
  | Add (a, b) -> sprintf "(%s + %s)"  (VarID.to_string a) (VarID.to_string b)
  | Sub (a, b) -> sprintf "(%s - %s)"  (VarID.to_string a) (VarID.to_string b)
  | Mul (a, b) -> sprintf "(%s * %s)"  (VarID.to_string a) (VarID.to_string b)
  | Div (a, b) -> sprintf "(%s / %s)"  (VarID.to_string a) (VarID.to_string b)
  | Mod (a, b) -> sprintf "(%s %% %s)" (VarID.to_string a) (VarID.to_string b)
  | Neg a -> sprintf "(- %s)" (VarID.to_string a)
  | IfEq (a, b, c, d) | IfLess (a, b, c, d) ->
      sprintf "%sif %s %s %s then\n%s%s\n%selse\n%s%s"
        (make_indent indent_level)
        (VarID.to_string a)
        (match expr with IfEq _ -> "=" | IfLess _ -> "<" | _ -> assert false)
        (VarID.to_string b)
        (match c with Let _ | IfEq _ | IfLess _ -> "" | _ -> (make_indent (indent_level + 1)))
        (string_of_expr ~indent_level:(indent_level + 1) c)
        (make_indent indent_level)
        (match d with Let _ | IfEq _ | IfLess _ -> "" | _ -> (make_indent (indent_level + 1)))
        (string_of_expr ~indent_level:(indent_level + 1) d)
  | Var a ->
      VarID.to_string a
  | Let (a, b, c) ->
      begin match b with
      | Let _ | IfEq _ | IfLess _ ->
          sprintf "%slet %s =\n%s\n%sin\n%s%s"
            (make_indent indent_level)
            (VarID.to_string a)
            (string_of_expr ~indent_level:(indent_level + 1) b)
            (make_indent indent_level)
            (match c with | Let _ | IfEq _ | IfLess _ -> "" | _ -> (make_indent indent_level))
            (string_of_expr ~indent_level c)
      | _ ->
          sprintf "%slet %s = %s in\n%s%s"
            (make_indent indent_level)
            (VarID.to_string a)
            (string_of_expr ~indent_level b)
            (match c with | Let _ | IfEq _ | IfLess _ -> "" | _ -> (make_indent indent_level))
            (string_of_expr ~indent_level c)
      end
  | ApplyKnown (f, args) ->
      sprintf "apply(%s %s)" (VarID.to_string f) (String.concat " " (List.map VarID.to_string args))
  | ApplyUnknown (f, args) ->
      sprintf "apply_uk(%s %s)" (VarID.to_string f) (String.concat " " (List.map VarID.to_string args))
  | RefArrayAlloc (a, b) ->
      sprintf "ref_array_alloc(%s, %s)" (VarID.to_string a) (VarID.to_string b)
  | ValArrayAlloc (a, b) ->
      sprintf "val_array_alloc(%s, %s)" (VarID.to_string a) (VarID.to_string b)
  | RefClone a ->
      sprintf "clone(%s)" (VarID.to_string a)
  | RefRelease a ->
      sprintf "release(%s)" (VarID.to_string a)
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
      | _  -> String.concat " -> " (List.map (fun x -> VarID.to_string x.Normal.var_id) f_args)
      end) ^
    (string_of_expr f_body) ^
    (sprintf "\nEND FUNCTION (source name: %s)" f.f_name)
  | NativeClosure (free_vars_array, f_args, f_body) ->
    (sprintf "BEGIN CLOSURE (source name: %s) ==> %s : %s =\n"
      f.f_name
      (VarID.to_string id)
      begin match f_args with
      | [] -> "()"
      | _  -> String.concat " -> " (List.map (fun x -> VarID.to_string x.Normal.var_id) f_args)
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


let value_var a = {Normal.storage = Normal.Value; Normal.var_id = a}
let ref_var a   = {Normal.storage = Normal.Ref;   Normal.var_id = a}


(* Compute the set of all free variables found in a function definition.  (If the set
 * is nonempty, we'll have to do closure conversion. *)
let rec free_variables ?(acc=SPVSet.empty) (f_args : SPVSet.t) (f_body : Normal.t) : SPVSet.t =
  let accum_free vars =
    List.fold_left
      (fun acc x -> if SPVSet.mem x f_args then acc else SPVSet.add x acc)
      acc
      vars
  in
  match f_body with
  | Normal.Unit | Normal.Int _ | Normal.External _ ->
      acc
  | Normal.Add (a, b) | Normal.Sub (a, b) | Normal.Mul (a, b)
  | Normal.Div (a, b) | Normal.Mod (a, b) ->
      let a_val = value_var a in
      let b_val = value_var b in
      accum_free [a_val; b_val]
  | Normal.Neg a ->
      let a_val = value_var a in accum_free [a_val]
  | Normal.Var a ->
      accum_free [a]
  | Normal.IfEq (a, b, e1, e2) | Normal.IfLess (a, b, e1, e2) ->
      let a_val = value_var a in
      let b_val = value_var b in
      let e1_free = free_variables ~acc f_args e1 in
      let e2_free = free_variables ~acc f_args e2 in
      let e1_e2_free = SPVSet.union e1_free e2_free in
      SPVSet.union e1_e2_free (accum_free [a_val; b_val])
  | Normal.Let (a, e1, e2) ->
      let e1_free = free_variables ~acc f_args e1 in
      let e2_free = free_variables ~acc (SPVSet.add a f_args) e2 in
      SPVSet.union e1_free e2_free
  | Normal.LetFun (_, g, g_args, g_body, g_scope_expr) ->
      (* LetFun is a recursive form, so [g] is bound in its body. *)
      let f_and_g_args = List.fold_left
        (fun acc x -> SPVSet.add x acc)
        f_args
        g_args
      in
      let g_body_free  = free_variables ~acc (SPVSet.add (value_var g) f_and_g_args) g_body in
      let g_scope_free = free_variables ~acc (SPVSet.add (value_var g) f_args) g_scope_expr in
      SPVSet.union g_body_free g_scope_free
  | Normal.Apply (g, g_args) ->
      accum_free ((value_var g) :: g_args)
  | Normal.RefArrayAlloc (a, b) ->
      let a_val = value_var a in
      let b_val = ref_var b in
      accum_free [a_val; b_val]
  | Normal.ValArrayAlloc (a, b) ->
      let a_val = value_var a in
      let b_val = value_var b in
      accum_free [a_val; b_val]
  | Normal.RefClone a ->
      let a_val = ref_var a in accum_free [a_val]
  | Normal.RefArraySet (a, b, c) ->
      let a_val = ref_var a in
      let b_val = value_var b in
      let c_val = ref_var c in
      accum_free [a_val; b_val; c_val]
  | Normal.ValArraySet (a, b, c) ->
      let a_val = ref_var a in
      let b_val = value_var b in
      let c_val = value_var c in
      accum_free [a_val; b_val; c_val]
  | Normal.RefArrayGet (a, b) | Normal.ValArrayGet (a, b) ->
      let a_val = ref_var a in
      let b_val = value_var b in
      accum_free [a_val; b_val]



(* Insert RefRelease calls to clean up the list of [refs] before evaluating the [expr]. *)
let rec insert_refs_release refs expr =
  match refs with
  | []          -> expr
  | ref :: tail -> Let (Normal.free_var (), RefRelease ref, insert_refs_release tail expr)


(* Construct a closure.  The code which defines the function is transformed into code which
 * allocates an array and stores its free variables into the array.
 *
 * FIXME: the [scope_expr] needs to be modified so that references to [f_id] are
 * replaced with the [closure_id].  The difficulty here is that [f_id] is a value type
 * but [closure_id] is a reference type.  The most important case to consider is when [f_id] is
 * assigned to a variable for later use.
 *
 * This problem can probably be reduced if all functions are boxed as a closure the moment they get
 * bound to a variable (causing "unknown function" calls). *)
let make_closure 
  (f_id : var_t)           (* Function identifier *)
  (closure_id : var_t)     (* Identifier to use for the closure storage array *)
  (free_vars : SPVSet.t)   (* Set of free variables to close over *)
  (scope_expr : Normal.t)  (* Expression in which the closure will be in scope *)
    : Normal.t =
  (* Prefix the expression with all the array_set operations necessary to init the closure *)
  let (_, expr_with_array_init) = SPVSet.fold
    (fun x (ofs, exp) ->
      let array_set_expr =
        match x.Normal.storage with
        | Normal.Value ->
            (* Value types are boxed so they can be stored in a reference array. *)
            let size_id = value_var (Normal.free_var ()) in
            let box_id  = ref_var   (Normal.free_var ()) in
            let ofs_id  = value_var (Normal.free_var ()) in
            Normal.Let (size_id, Normal.Int 1,
              Normal.Let (box_id,
                Normal.ValArrayAlloc (size_id.Normal.var_id, x.Normal.var_id),
                Normal.Let (ofs_id, Normal.Int ofs,
                  Normal.Let (value_var (Normal.free_var ()),
                    Normal.RefArraySet (closure_id, ofs_id.Normal.var_id, box_id.Normal.var_id),
                    exp))))
        | Normal.Ref ->
            (* Reference types are stored directly. *)
            let ofs_id = value_var (Normal.free_var ()) in
            Normal.Let (ofs_id, Normal.Int ofs,
              Normal.Let (value_var (Normal.free_var ()),
                Normal.RefArraySet (closure_id, ofs_id.Normal.var_id, x.Normal.var_id),
                exp))
      in
      (ofs + 1, array_set_expr))
    free_vars
    (1, scope_expr)
  in
  (* Now prepend the closure array allocation.  Note that array location zero holds the closure
   * function itself (boxed), so that the entire closure can be passed around as a first-class
   * value. *)
  let closure_func_ref = ref_var   (Normal.free_var ()) in
  let box_size_id      = value_var (Normal.free_var ()) in
  let closure_size_id  = value_var (Normal.free_var ()) in
  Normal.Let (box_size_id, Normal.Int 1,
    Normal.Let (closure_func_ref, Normal.ValArrayAlloc (box_size_id.Normal.var_id, f_id),
      Normal.Let (closure_size_id, Normal.Int (1 + (SPVSet.cardinal free_vars)),
        Normal.Let (ref_var closure_id,
          Normal.RefArrayAlloc (closure_size_id.Normal.var_id, closure_func_ref.Normal.var_id),
          expr_with_array_init))))



(* Extract function bodies from the expression tree, and simultaneously insert code to implicitly release
 * references as they fall out of scope. *)
let rec extract_functions_aux
  (local_refs : var_t list)   (* List of live references which must be released at end-of-expr *)
  (recur_ids : SPVSet.t)      (* Function ids which could be referenced recursively in this expr *)
  (normal_expr : Normal.t)    (* Expression to process *)
    : expr_t =                (* Resulting expression, with functions extracted *)
  match normal_expr with
  | Normal.Unit       -> insert_refs_release local_refs Unit
  | Normal.Int x      -> insert_refs_release local_refs (Int x)
  | Normal.Add (a, b) -> insert_refs_release local_refs (Add (a, b))
  | Normal.Sub (a, b) -> insert_refs_release local_refs (Sub (a, b))
  | Normal.Mul (a, b) -> insert_refs_release local_refs (Mul (a, b))
  | Normal.Div (a, b) -> insert_refs_release local_refs (Div (a, b))
  | Normal.Mod (a, b) -> insert_refs_release local_refs (Mod (a, b))
  | Normal.Neg a      -> insert_refs_release local_refs (Neg a)
  | Normal.Var {Normal.storage = _; Normal.var_id = a} ->
      (* When the value of an expression is a variable containing a reference type,
       * we allow the reference to escape without being released.  The containing
       * expression takes ownership of this reference. *)
      let other_refs = List.filter (fun ref -> ref <> a) local_refs in
      insert_refs_release other_refs (Var a)

  | Normal.IfEq (a, b, e1, e2) ->
      IfEq (a, b, extract_functions_aux local_refs recur_ids e1,
        extract_functions_aux local_refs recur_ids e2)
  | Normal.IfLess (a, b, e1, e2) ->
      IfLess (a, b, extract_functions_aux local_refs recur_ids e1,
        extract_functions_aux local_refs recur_ids e2)

  | Normal.Let ({Normal.storage = Normal.Ref; Normal.var_id = a}, e1, e2) ->
      (* When binding to a reference type, we will have to release the reference at end-of-scope. *)
      Let (a, extract_functions_aux [] recur_ids e1,
        extract_functions_aux (a :: local_refs) recur_ids e2)
  | Normal.Let ({Normal.storage = Normal.Value; Normal.var_id = a}, e1, e2) ->
      Let (a, extract_functions_aux [] recur_ids e1, extract_functions_aux local_refs recur_ids e2)

  | Normal.LetFun (f_name, f_id, f_args, f_body, f_scope_expr) ->
      let recur_ids = SPVSet.add (value_var f_id) recur_ids in
      let f_arg_set = List.fold_left (fun acc x -> SPVSet.add x acc) SPVSet.empty f_args in
      let free_vars = free_variables (SPVSet.union recur_ids f_arg_set) f_body in
      let body_extracted = extract_functions_aux [] recur_ids f_body in
      if SPVSet.is_empty free_vars then
        let () = add_function_def f_id {f_name; f_impl = NativeFunc (f_args, body_extracted)} in
        extract_functions_aux local_refs recur_ids f_scope_expr
      else
        (* Closure conversion. *)
        let closure_id = Normal.free_var () in
        let closure_expr = make_closure f_id closure_id free_vars f_scope_expr in
        let () = add_function_def f_id {f_name; f_impl = NativeClosure (closure_id, f_args, body_extracted)} in
        extract_functions_aux local_refs recur_ids closure_expr
  | Normal.External (f_name, f_id, f_ext_impl, f_arg_count, f_scope_expr) ->
      let recur_ids = SPVSet.add (value_var f_id) recur_ids in
      let () = add_function_def f_id {f_name; f_impl = ExtFunc (f_ext_impl, f_arg_count)} in
      extract_functions_aux local_refs recur_ids f_scope_expr
  | Normal.Apply (f_id, f_args) ->
      (* TODO: closure detection *)
      let f_arg_ids = List.map (fun x -> x.Normal.var_id) f_args in
      if (VMap.mem f_id !function_defs) || (SPVSet.mem (value_var f_id) recur_ids) then
        ApplyKnown (f_id, f_arg_ids)
      else
        ApplyUnknown (f_id, f_arg_ids)

  | Normal.RefArrayAlloc (size, init) ->
      insert_refs_release local_refs (RefArrayAlloc (size, init))
  | Normal.ValArrayAlloc (size, init) ->
      insert_refs_release local_refs (ValArrayAlloc (size, init))
  | Normal.RefClone a ->
      (* Make sure we clone the reference prior to releasing it *)
      let clone_ref = Normal.free_var () in
      Let (clone_ref, RefClone a, insert_refs_release local_refs (Var clone_ref))
  | Normal.RefArraySet (arr, index, x) ->
      (* Make sure we perform array operations prior ot releasing the array *)
      Let (Normal.free_var (), RefArraySet (arr, index, x), insert_refs_release local_refs Unit)
  | Normal.ValArraySet (arr, index, x) ->
      (* Make sure we perform array operations prior ot releasing the array *)
      Let (Normal.free_var (), ValArraySet (arr, index, x), insert_refs_release local_refs Unit)
  | Normal.RefArrayGet (arr, index) ->
      (* Make sure we perform array operations prior ot releasing the array *)
      Let (Normal.free_var (), RefArrayGet (arr, index), insert_refs_release local_refs Unit)
  | Normal.ValArrayGet (arr, index) ->
      (* Make sure we perform array operations prior ot releasing the array *)
      Let (Normal.free_var (), ValArrayGet (arr, index), insert_refs_release local_refs Unit)


(* Rewrite a normalized expression tree as a list of function definitions and an entry point. *)
let extract_functions (expr : Normal.t) : t =
  let () = reset_function_defs () in
  let toplevel_expr = extract_functions_aux [] SPVSet.empty expr in
  (* Construct the program entry point, [zml_main : unit -> unit] *)
  let () = add_function_def Normal.reserved_main_id
    {f_name = "zml_main"; f_impl = NativeFunc ([], toplevel_expr)}
  in
  {functions = !function_defs; entry_point=Normal.reserved_main_id}


