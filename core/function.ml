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
  | RefRelease of var_t                       (* Drop ownership of a reference *)
  | RefArraySet of var_t * int * var_t        (* Store a reference in a ref array (arr, index, ref) *)
  | ValArraySet of var_t * int * var_t        (* Store a value in a value array (arr, index, val) *)
  | RefArrayGet of var_t * int                (* Get a reference from a ref array *)
  | ValArrayGet of var_t * int                (* Get a value from a value array *)


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


let rec string_of_expr (expr : expr_t) : string =
  match expr with
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
      (VarID.to_string a) (VarID.to_string b) (string_of_expr c) (string_of_expr d)
  | IfLess (a, b, c, d) ->
      sprintf "if %s < %s then\n    %s\nelse\n    %s\n"
      (VarID.to_string a) (VarID.to_string b) (string_of_expr c) (string_of_expr d)
  | Var a -> VarID.to_string a
  | Let (a, b, c) ->
      sprintf "let %s = %s in\n%s" (VarID.to_string a) (string_of_expr b) (string_of_expr c)
  | ApplyKnown (f, args) ->
      sprintf "apply(%s %s)" (VarID.to_string f) (String.concat " " (List.map VarID.to_string args))
  | ApplyUnknown (f, args) ->
      sprintf "apply_uk(%s %s)" (VarID.to_string f) (String.concat " " (List.map VarID.to_string args))
  | RefArrayAlloc (n, a) ->
      sprintf "ref_array_alloc(%d, %s)" n (VarID.to_string a)
  | ValArrayAlloc (n, a) ->
      sprintf "val_array_alloc(%d, %s)" n (VarID.to_string a)
  | RefRelease a ->
      sprintf "release(%s)" (VarID.to_string a)
  | RefArraySet (a, n, b) ->
      sprintf "ref_array_set(%s, %d, %s)" (VarID.to_string a) n (VarID.to_string b)
  | ValArraySet (a, n, b) ->
      sprintf "val_array_set(%s, %d, %s)" (VarID.to_string a) n (VarID.to_string b)
  | RefArrayGet (a, n) ->
      sprintf "ref_array_get(%s, %d)" (VarID.to_string a) n
  | ValArrayGet (a, n) ->
      sprintf "val_array_get(%s, %d)" (VarID.to_string a) n



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


(* Wrap a variable id with a Value type identifier. *)
let value_var a = {Normal.storage = Normal.Value; Normal.var_id = a}

(* Compute the set of all free variables found in a function definition.  (If the set
 * is nonempty, we'll have to do closure conversion. *)
let rec free_variables ?(acc=SPVSet.empty) (f_args : SPVSet.t) (f_body : Normal.t) : SPVSet.t =
  match f_body with
  | Normal.Unit | Normal.Int _ | Normal.External _ ->
      acc
  | Normal.Add (a, b) | Normal.Sub (a, b) | Normal.Mul (a, b)
  | Normal.Div (a, b) | Normal.Mod (a, b) ->
      let a_val = value_var a in
      let b_val = value_var b in
      let a_free  = if SPVSet.mem a_val f_args then acc    else SPVSet.add a_val acc in
      let ab_free = if SPVSet.mem b_val f_args then a_free else SPVSet.add b_val a_free in
      ab_free
  | Normal.Neg a ->
      let a_val = value_var a in
      if SPVSet.mem a_val f_args then acc else SPVSet.add a_val acc
  | Normal.Var a ->
      if SPVSet.mem a f_args then acc else SPVSet.add a acc
  | Normal.IfEq (a, b, e1, e2) | Normal.IfLess (a, b, e1, e2) ->
      let a_val = value_var a in
      let b_val = value_var b in
      let e1_free = free_variables ~acc f_args e1 in
      let e2_free = free_variables ~acc f_args e2 in
      let e1_e2_free = SPVSet.union e1_free e2_free in
      let a_free  = if SPVSet.mem a_val f_args then e1_e2_free else SPVSet.add a_val e1_e2_free in
      let ab_free = if SPVSet.mem b_val f_args then a_free     else SPVSet.add b_val a_free in
      ab_free
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
      List.fold_left
        (fun free x -> if SPVSet.mem x f_args then free else SPVSet.add x free)
        acc
        ((value_var g) :: g_args)


(* Insert code to drop a reference after evaluation of a subexpression. *)
let with_ref_release (var : var_t) (expr : expr_t) =
  let x = Normal.free_var () in
  Let (x, expr, Let (Normal.free_var (), RefRelease var, Var x))


(* Construct a closure.  The code which defines the function is transformed into code which
 * allocates an array and stores its free variables into the array. *)
let make_closure 
  (f_id : var_t)           (* Function identifier *)
  (closure_id : var_t)     (* Identifier to use for the closure storage array *)
  (free_vars : SPVSet.t)   (* Set of free variables to close over *)
  (scope_expr : expr_t)    (* Expression in which the closure will be in scope *)
    =
  (* Prefix the expression with all the array_set operations necessary to init the closure *)
  let (_, expr_with_array_init) = SPVSet.fold
    (fun x (ofs, exp) ->
      let array_set_expr =
        match x.Normal.storage with
        | Normal.Value ->
            (* Value types are boxed so they can be stored in a reference array. *)
            let box_id = Normal.free_var () in
            Let (box_id,
              ValArrayAlloc (1, x.Normal.var_id),
                Let (Normal.free_var (), RefArraySet (closure_id, ofs, box_id),
                  Let (Normal.free_var (), RefRelease box_id,
                    exp)))
        | Normal.Ref ->
            (* Reference types are stored directly. *)
            Let (Normal.free_var (), RefArraySet (closure_id, ofs, x.Normal.var_id), exp)
      in
      (ofs + 1, array_set_expr))
    free_vars
    (1, scope_expr)
  in
  (* Now prepend the closure array allocation, and append the closure array release.  Note
   * that array location zero holds the closure function itself (boxed), so that the entire
   * closure can be passed around as a first-class value. *)
  let closure_func_ref = Normal.free_var () in
  Let (closure_func_ref, ValArrayAlloc (1, f_id),
    Let (closure_id, (RefArrayAlloc (1 + (SPVSet.cardinal free_vars), closure_func_ref)),
      Let (Normal.free_var (), RefRelease closure_func_ref,
        with_ref_release closure_id expr_with_array_init)))


let rec extract_functions_aux
  (recur_ids : SPVSet.t)      (* Function ids which could be referenced recursively in this expr *)
  (normal_expr : Normal.t)    (* Expression to process *)
    : expr_t =                (* Resulting expression, with functions extracted *)
  match normal_expr with
  | Normal.Unit       -> Unit
  | Normal.Int x      -> Int x
  | Normal.Add (a, b) -> Add (a, b)
  | Normal.Sub (a, b) -> Sub (a, b)
  | Normal.Mul (a, b) -> Mul (a, b)
  | Normal.Div (a, b) -> Div (a, b)
  | Normal.Mod (a, b) -> Mod (a, b)
  | Normal.Neg a      -> Neg a
  | Normal.Var {Normal.storage = _; Normal.var_id = a} ->
      Var a

  | Normal.IfEq (a, b, e1, e2) ->
      IfEq (a, b, extract_functions_aux recur_ids e1, extract_functions_aux recur_ids e2)
  | Normal.IfLess (a, b, e1, e2) ->
      IfLess (a, b, extract_functions_aux recur_ids e1, extract_functions_aux recur_ids e2)
  | Normal.Let ({Normal.storage = _; Normal.var_id = a}, e1, e2) ->
      Let (a, extract_functions_aux recur_ids e1, extract_functions_aux recur_ids e2)

  | Normal.LetFun (f_name, f_id, f_args, f_body, f_scope_expr) ->
      let recur_ids = SPVSet.add (value_var f_id) recur_ids in
      let f_arg_set = List.fold_left (fun acc x -> SPVSet.add x acc) SPVSet.empty f_args in
      let free_vars = free_variables (SPVSet.union recur_ids f_arg_set) f_body in
      let body_extracted = extract_functions_aux recur_ids f_body in
      if SPVSet.is_empty free_vars then
        let () = add_function_def f_id {f_name; f_impl = NativeFunc (f_args, body_extracted)} in
        extract_functions_aux recur_ids f_scope_expr
      else
        (* Closure conversion. *)
        let closure_id = Normal.free_var () in
        let () = add_function_def f_id {f_name; f_impl = NativeClosure (closure_id, f_args, body_extracted)} in
        let scope_extracted = extract_functions_aux recur_ids f_scope_expr in
        make_closure f_id closure_id free_vars scope_extracted
  | Normal.External (f_name, f_id, f_ext_impl, f_arg_count, f_scope_expr) ->
      let recur_ids = SPVSet.add (value_var f_id) recur_ids in
      let () = add_function_def f_id {f_name; f_impl = ExtFunc (f_ext_impl, f_arg_count)} in
      extract_functions_aux recur_ids f_scope_expr
  | Normal.Apply (f_id, f_args) ->
      (* TODO: closure detection *)
      let f_arg_ids = List.map (fun x -> x.Normal.var_id) f_args in
      if (VMap.mem f_id !function_defs) || (SPVSet.mem (value_var f_id) recur_ids) then
        ApplyKnown (f_id, f_arg_ids)
      else
        ApplyUnknown (f_id, f_arg_ids)


(* Rewrite a normalized expression tree as a list of function definitions and an entry point. *)
let extract_functions (expr : Normal.t) : t =
  let () = reset_function_defs () in
  let toplevel_expr = extract_functions_aux SPVSet.empty expr in
  (* Construct the program entry point, [zml_main : unit -> unit] *)
  let () = add_function_def Normal.reserved_main_id
    {f_name = "zml_main"; f_impl = NativeFunc ([], toplevel_expr)}
  in
  {functions = !function_defs; entry_point=Normal.reserved_main_id}


