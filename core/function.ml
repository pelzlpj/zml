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

module VarID = Normal.VarID
module VMap  = Normal.VMap
module VSet  = Normal.VSet
type var_t   = Normal.var_t


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
  | Apply of var_t * (var_t list)             (* Function application *)


type function_def_t =
  | NativeFunc of (var_t list) * expr_t     (* Function defined in ZML (function args, function body) *)
  | ExtFunc of string                       (* Function defined in ASM (with ASM identifier) *)

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
  | Apply (f, args) ->
      sprintf "apply(%s %s)" (VarID.to_string f) (String.concat " " (List.map VarID.to_string args))


let string_of_function id (f : function_t) : string =
  match f.f_impl with
  | NativeFunc (f_args, f_body) ->
    (sprintf "BEGIN FUNCTION (source name: %s) ==> %s : %s =\n"
      f.f_name
      (VarID.to_string id)
      begin match f_args with
      | [] -> "()"
      | _  -> String.concat " -> " (List.map VarID.to_string f_args)
      end) ^
    (string_of_expr f_body) ^
    (sprintf "\nEND FUNCTION (source name: %s)" f.f_name)
  | ExtFunc ext_impl ->
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


(* Deterine whether or not a function definition has free variables.  If so, we'll need to do
 * closure conversion. *)
let rec has_free_variables (f_args : var_t list) (f_body : Normal.t) =
  match f_body with
  | Normal.Unit | Normal.Int _ | Normal.External _ ->
      false
  | Normal.Add (a, b) | Normal.Sub (a, b) | Normal.Mul (a, b)
  | Normal.Div (a, b) | Normal.Mod (a, b) ->
      (not (List.mem a f_args)) || (not (List.mem b f_args))
  | Normal.Neg a | Normal.Var a ->
      not (List.mem a f_args)
  | Normal.IfEq (a, b, e1, e2) | Normal.IfLess (a, b, e1, e2) ->
      (not (List.mem a f_args)) || (not (List.mem b f_args)) ||
        (has_free_variables f_args e1) || (has_free_variables f_args e2)
  | Normal.Let (a, e1, e2) ->
      (has_free_variables f_args e1) || (has_free_variables (a :: f_args) e2)
  | Normal.LetFun (_, g, g_args, g_body, g_scope_expr) ->
      (* LetFun is a recursive form, so [g] is bound in the body. *)
      (has_free_variables (List.rev_append g_args (g :: f_args)) g_body) ||
        (has_free_variables (g :: f_args) g_scope_expr)
  | Normal.Apply (g, g_args) ->
      List.exists
        (fun a -> not (List.mem a f_args))
        (g :: g_args)



let rec extract_functions_aux
  (recur_ids : VSet.t)        (* function ids which could be referenced recursively in this expr *)
  (normal_expr : Normal.t)    (* expression to process *)
    : expr_t =                (* resulting expression, with functions extracted *)
  match normal_expr with
  | Normal.Unit       -> Unit
  | Normal.Int x      -> Int x
  | Normal.Add (a, b) -> Add (a, b)
  | Normal.Sub (a, b) -> Sub (a, b)
  | Normal.Mul (a, b) -> Mul (a, b)
  | Normal.Div (a, b) -> Div (a, b)
  | Normal.Mod (a, b) -> Mod (a, b)
  | Normal.Neg a      -> Neg a
  | Normal.Var a      -> Var a

  | Normal.IfEq (a, b, e1, e2) ->
      IfEq (a, b, extract_functions_aux recur_ids e1, extract_functions_aux recur_ids e2)
  | Normal.IfLess (a, b, e1, e2) ->
      IfLess (a, b, extract_functions_aux recur_ids e1, extract_functions_aux recur_ids e2)
  | Normal.Let (a, e1, e2) ->
      Let (a, extract_functions_aux recur_ids e1, extract_functions_aux recur_ids e2)

  | Normal.LetFun (f_name, f_id, f_args, f_body, f_scope_expr) ->
      (* TODO: closure conversion *)
      let () = assert (not (has_free_variables (f_id :: f_args) f_body)) in
      let recur_ids = VSet.add f_id recur_ids in
      let body_extracted = extract_functions_aux recur_ids f_body in
      let () = add_function_def f_id {f_name; f_impl = NativeFunc (f_args, body_extracted)} in
      extract_functions_aux recur_ids f_scope_expr
  | Normal.External (f_name, f_id, f_ext_impl, f_scope_expr) ->
      let recur_ids = VSet.add f_id recur_ids in
      let () = add_function_def f_id {f_name; f_impl = ExtFunc f_ext_impl} in
      extract_functions_aux recur_ids f_scope_expr
  | Normal.Apply (f_id, f_args) ->
      (* TODO: detect known functions versus unknown functions versus closures *)
      let () = assert ((VMap.mem f_id !function_defs) || (VSet.mem f_id recur_ids)) in
      Apply (f_id, f_args)


(* Rewrite a normalized expression tree as a list of function definitions and an entry point. *)
let extract_functions (expr : Normal.t) : t =
  let () = reset_function_defs () in
  let toplevel_expr = extract_functions_aux VSet.empty expr in
  (* Construct the program entry point, [zml_main : unit -> unit] *)
  let () = add_function_def Normal.reserved_main_id
    {f_name = "zml_main"; f_impl = NativeFunc ([], toplevel_expr)}
  in
  {functions = !function_defs; entry_point=Normal.reserved_main_id}


