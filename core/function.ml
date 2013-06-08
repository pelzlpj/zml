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
type cond_t  = Normal.cond_t


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
  | Conditional of cond_t * var_t * var_t * t * t   (* Conditional form *)
  | Var of var_t                                    (* Bound variable reference (not a known function) *)
  | KnownFuncVar of var_t                           (* Known function reference *)
  | Let of var_t * t * t                            (* Let binding for a variable *)
  | ApplyKnown of var_t * (var_t list)              (* Application of "known" function *)
  | ApplyUnknown of var_t * (var_t list)            (* Application of an "unknown" function
                                                          (i.e. call to computed address) *)


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


(* Get the storage policy associated with a type.  (For function types, the resulting
 * storage policy is always Ref.) *)
let storage_of_type tp =
  match tp with
  | Type.Unit | Type.Bool _ | Type.Int _ ->
      Value
  | Type.Arrow _ ->
      (* Any first-class treatment of a function results in a closure reference. *)
      Ref
  | Type.Array _ ->
      Ref
  | Type.Var _ ->
      (* Polymorphic type... *)
      assert false


(* Use a variable's type information to infer its storage policy *)
let infer_storage (v : VarID.t) =
  {SPVar.id = v.VarID.id; SPVar.storage = storage_of_type v.VarID.tp}


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


(* Look up a function definition in the list of known functions.
 *
 * (This may fail when looking up a recursive function definition from
 * the context of the recursive function.  Other failures are
 * probably bugs...) *)
let find_function_def_by_id (id : SPVar.t) : function_t option =
  try
    Some (SPVMap.find id !function_defs)
  with Not_found ->
    None


(* Locate up a named external function in the list of known functions. *)
let find_ext_function_def_by_name (asm_name : string) : SPVar.t =
  let result =
    SPVMap.fold
      (fun id def result_opt ->
        match def.f_impl with
        | ExtFunc (name, _) when name = asm_name ->
            Some id
        | _ ->
            result_opt)
      !function_defs
      None
  in
  match result with
  | None ->
      let () = Printf.fprintf stderr "Missing asm function: %s\n" asm_name in
      assert false
  | Some x ->
      x


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
  (* Prefix the expression with all the array_init operations necessary to init the closure *)
  let array_init_one = find_ext_function_def_by_name Builtins.array_init_one in
  let (_, expr_with_array_init) = VSet.fold
    (fun free_var (ofs, exp) ->
      let array_set_expr =
        let ofs_id = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
        let sp_free_var = infer_storage free_var in
        let ref_flag_id = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
        Let (ofs_id, Int ofs,
          Let (ref_flag_id, Int (match ref_flag_id.SPVar.storage with Ref -> 1 | Value -> 0),
            Let ({SPVar.id = Normal.free_var (); SPVar.storage = Value},
              ApplyKnown (array_init_one, [closure_id; ofs_id; sp_free_var; ref_flag_id]),
              exp)))
      in
      (ofs + 1, array_set_expr))
    free_vars
    (1, extract_fun scope_expr)
  in
  (* Now prepend the closure array allocation.  Note that array location zero holds the closure
   * known-function itself, so that the entire closure can be passed around as a first-class
   * value. *)
  let closure_size_id   = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
  let known_func_ofs_id = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
  let known_func_id     = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
  let ref_flag_id       = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
  let array_alloc       = find_ext_function_def_by_name Builtins.array_alloc in
  Let (known_func_id, KnownFuncVar (value_var f_id),
    Let (closure_size_id, Int (1 + (VSet.cardinal free_vars)),
      Let (closure_id, ApplyKnown (array_alloc, [closure_size_id]),
        Let (known_func_ofs_id, Int 0,
          Let (ref_flag_id, Int 0,
            Let ({SPVar.id = Normal.free_var (); SPVar.storage = Value},
              ApplyKnown (array_init_one, [closure_id; known_func_ofs_id; known_func_id; ref_flag_id]),
              expr_with_array_init))))))


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
          let ofs_id = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
          let array_get_val = find_ext_function_def_by_name Builtins.array_get_val in
          let array_get_ref = find_ext_function_def_by_name Builtins.array_get_ref in
          Let (ofs_id, Int ofs,
            match storage_of_type free_var.VarID.tp with
            | Value ->
                Let (value_var free_var,
                  ApplyKnown (array_get_val, [closure_id; ofs_id]),
                  exp)
            | Ref ->
                Let (ref_var free_var,
                  ApplyKnown (array_get_ref, [closure_id; ofs_id]),
                  exp))
        in
        (ofs + 1, array_get_expr))
      free_vars
      (1, extract_fun body)
  in
  body_extracted


(* Insert code to invoke a closure. *)
let make_closure_application closure_id args =
  let closure_ofs_id = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
  let func_id        = {SPVar.id = Normal.free_var (); SPVar.storage = Value} in
  let array_get_val  = find_ext_function_def_by_name Builtins.array_get_val in
  Let (closure_ofs_id, Int 0,
    Let (func_id,
      ApplyKnown (array_get_val, [closure_id; closure_ofs_id]),
      ApplyUnknown (func_id, closure_id :: args)))


(* Insert a function definition generated by partial application of some other callable.
 * Given some code of the general form
 *
 *    let f x y z = ... in
 *    ...
 *    f a
 *
 * the following function is used to rewrite the source into the form
 *
 *    let f x y z = ... in
 *    ...
 *    let g y' z' = f a y' z' in
 *    g
 *
 * The newly-defined function [g] will be recognized as a closure due to the presence of free
 * variable [a] in its body. *)
let make_partial_application
  (f_id : VarID.t)                (* Function being partially applied *)
  (supplied_args : VarID.t list)  (* Partial argument list supplied to [f_id] *)
    : Normal.t =
  (* Construct a dummy list of arguments to [f_id] which are *not* supplied by the [supplied_args]. *)
  let rec build_missing_args f_type present_args missing_args =
    match f_type with
    | Type.Arrow (arg_type, next_type) ->
        begin match present_args with
        | [] ->
            let arg_id = {VarID.id = Normal.free_var (); VarID.tp = arg_type} in
            build_missing_args next_type present_args (arg_id :: missing_args)
        | arg :: tail ->
            build_missing_args next_type tail missing_args
        end
    | _ ->
        List.rev missing_args
  in
  let partial_id   = {f_id with VarID.id = Normal.free_var ()} in
  let partial_name = (VarID.to_string f_id) ^ "_partial" in
  let partial_args = build_missing_args f_id.VarID.tp supplied_args [] in
  Normal.LetFun (partial_name, partial_id, partial_args,
    Normal.Apply (f_id, supplied_args @ partial_args),
    Normal.Var partial_id)


(* Determines whether or not the function with the given [f_id] is ever treated as a first-class
 * citizen within the given [expr]--in other words, whether it is ever used in any way other than
 * simply calling it with a full argument list. *)
let rec is_first_class f_id (expr : Normal.t) : bool =
  match expr with
  | Normal.Unit | Normal.Int _ ->
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


(* array_get operations take two different code paths: one for retrieving an element from
 * a reference array and one for retrieving an element from a value array.  Types are erased
 * in Function.t, so this is the last opportunity to differentiate based on type. *)
let rewrite_type_differentiated_builtins
  (sp_f_id   : SPVar.t)
  (f_args    : VarID.t list)
  (sp_f_args : SPVar.t list)
    : t =
  let orig_def_opt = find_function_def_by_id sp_f_id in
  match orig_def_opt with
  | Some {f_impl = ExtFunc (asm_name, _); _} when asm_name = Builtins.array_get ->
      (* FIXME: Each of these lookups is O(number of functions in program).  They should be collected
       * once and cached. *)
      let array_get_val = find_ext_function_def_by_name Builtins.array_get_val in
      let array_get_ref = find_ext_function_def_by_name Builtins.array_get_ref in
      begin match f_args with
      | {VarID.tp = Type.Array contained_type; _} :: _ ->
          begin match storage_of_type contained_type with
          | Ref ->
              ApplyKnown (array_get_ref, sp_f_args)
          | Value ->
              ApplyKnown (array_get_val, sp_f_args)
          end
      | _ ->
          assert false
      end
  | _ ->
      ApplyKnown (sp_f_id, sp_f_args)


type call_t = Known | Closure of var_t

(* Extract function bodies from the expression tree, storing them in the [function_defs] map. *)
let rec extract_functions_aux
  (callable_ids : call_t VMap.t)  (* Function ids which could be referenced in this expr *)
  (normal_expr  : Normal.t)       (* Expression to process *)
    : t =                         (* Resulting expression, with functions extracted *)
  match normal_expr with
  | Normal.Unit  -> Unit
  | Normal.Int x -> Int x
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
      if not (is_first_class f_id f_scope_expr) then
        (* Known-function optimization.  This is an externally-defined function which is always
         * invoked directly, so we don't need to box it in a closure array. *)
        let callable_ids = VMap.add f_id Known callable_ids in
        let () = add_function_def (value_var f_id) {f_name; f_impl = ExtFunc (f_ext_impl, f_arg_count)} in
        extract_functions_aux callable_ids f_scope_expr
      else
        (* Closure conversion.  This is an externally-defined function which gets stored at least
         * once as a function pointer.  Consequently we need to box it in a closure array, so that
         * the function pointer may be safely invoked by ApplyUnknown. *)
        let closure_id = {SPVar.id = Normal.free_var (); SPVar.storage = Ref} in
        let callable_ids = VMap.add f_id (Closure closure_id) callable_ids in
        let () = add_function_def (value_var f_id) {f_name; f_impl = ExtFunc (f_ext_impl, f_arg_count)} in
        make_closure_def f_id closure_id VSet.empty f_scope_expr (extract_functions_aux callable_ids)
  | Normal.Apply (f_id, f_args) ->
      let exp_arg_count = Normal.count_arrow_type_args f_id.VarID.tp in
      let act_arg_count = List.length f_args in
      if act_arg_count < exp_arg_count then
        (* Partial application.  We will handle this by rewriting the expression as a new function
         * declaration which contains free variables, resulting in closure creation. *)
        extract_functions_aux callable_ids (make_partial_application f_id f_args)
      else
        (* Complete application. *)
        let sp_f_args = List.map infer_storage f_args in
        begin try
          match VMap.find f_id callable_ids with
          | Known ->
              rewrite_type_differentiated_builtins (value_var f_id) f_args sp_f_args
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


