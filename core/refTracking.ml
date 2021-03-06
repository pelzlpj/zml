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


(* Management of variable lifetimes for reference types.
 *
 * ZML's initial target is the Z-Machine, which is a pretty weird VM.  Of particular note: the
 * function call stack is largely inaccessible, which makes it impossible to scan the stack for GC
 * roots.  The workaround is to track reference types explicitly.
 *
 * To this end, the ZML runtime registers references in a global roots table whenever a new
 * reference is created (allocating an array, retrieving a reference from an array-of-references,
 * etc.).  The code which calls into the runtime must explicitly release these references when they
 * fall out of scope.
 *
 * This module examines the code emitted by [Function.extract_functions], and inserts the code
 * necessary to release references.  The simple approach here would be to use let-binding scope to
 * determine when references should be released.  In an attempt to conserve heap memory and reduce
 * the size of the reference table, we try to do better than the simple approach: liveness analysis
 * is used to determine when reference types are no longer used, and these references are released
 * as soon as possible.
 *
 * General rules for reference management:
 *    - A new reference is created when allocating a reference type (list, array, etc.).
 *    - A new reference is created when retrieving a value from a data structure which stores
 *        reference types.
 *    - A new reference is created (as a clone) when a Let expression binds to a variable
 *        which was already bound to a reference type.
 *    - All references created within the scope of a function are released as soon as
 *        liveness analysis indicates that they are no longer used.  If a reference is
 *        the return value for a function, it is not released within function scope.
 *)

open Printf

module SPVar  = Function.SPVar
module SPVMap = Function.SPVMap
module SPVSet = Set.Make(SPVar)
type cond_t   = Function.cond_t


module type OPAQUE_ID = sig
  type t
  val compare : t -> t -> int
  val of_var : SPVar.t -> t
  val to_string : t -> string
  val to_int_string : t -> string
end


(* Opaque identifier for value-type variables *)
module ValID : OPAQUE_ID = struct
  type t = int
  let compare a b = if a < b then -1 else if a > b then 1 else 0
  let of_var x = match x.SPVar.storage with Function.Value -> x.SPVar.id | Function.Ref -> assert false
  let to_string x = sprintf "vv%d" x
  let to_int_string x = sprintf "%d" x
end

module VMap = Map.Make(ValID)


(* Opaque identifier for reference-type variables *)
module RefID : OPAQUE_ID = struct
  type t = int
  let compare a b = if a < b then -1 else if a > b then 1 else 0
  let of_var x = match x.SPVar.storage with Function.Ref -> x.SPVar.id | Function.Value -> assert false
  let to_string x = sprintf "rv%d" x
  let to_int_string x = sprintf "%d" x
end

module RSet = Set.Make(RefID)


(* Opaque identifier for variables with arbitrary storage policy *)
type sp_var_t =
  | Value of ValID.t
  | Ref   of RefID.t

let string_of_sp_var x = match x with Value v -> ValID.to_string v | Ref r -> RefID.to_string r


type t = {
  (* Locally-unique identifier attached to this expression, for ease of constructing
   * a control-flow graph.  (The identifiers will be dropped in iR.ml.) *)
  id   : int;     
  expr : expr_t
}

and expr_t =
  | Unit                                        (* Unit literal *)
  | Int of int                                  (* Integer constant *)
  | Conditional of cond_t * ValID.t * ValID.t
      * t * t                                   (* Conditional form *)
  | Var of sp_var_t                             (* Bound variable reference (not a known function) *)
  | KnownFuncVar of ValID.t                     (* Known function reference *)
  | Let of sp_var_t * t * t                     (* Let binding for a variable *)
  | ApplyKnown of ValID.t * (sp_var_t list)     (* Application of "known" function *)
  | ApplyUnknown of ValID.t * (sp_var_t list)   (* Application of an "unknown" function (computed address) *)



type function_def_t =
  (* Standard function defined in ZML (function args, function body) *)
  | NativeFunc of (sp_var_t list) * t
  (* Function defined in ASM (with ASM identifier, arg count *)
  | ExtFunc of string * int


type function_t = {
  (** Name of the function (will be injected into the assembly to assist in debugging) *)
  f_name : string;
  f_impl : function_def_t
}

type program_t = {
  (* List of known functions, each indexed by a unique variable id *)
  functions   : function_t VMap.t;
  (* Function to be invoked as program entry point (with type "unit -> unit") *)
  entry_point : ValID.t
}


(* Formatting rules:
 *  - A newline always follows "in", "then", and "else", as well as the true/false
 *    clauses of if/then.
 *  - The bound expression in a Let is indented iff it is another Let or an If.
 *  - The "true" and "false" expressions in an if-then-else are both indented. *)
let rec string_of_expr ?(indent_level=0) ?(chars_per_indent=2) (expr : t) : string =
  let make_indent level = String.make (level * chars_per_indent) ' ' in
  match expr.expr with
  | Unit -> "()"
  | Int i -> string_of_int i
  | Conditional (cond, a, b, c, d) ->
      sprintf "%sif %s %s %s then\n%s%s\n%selse\n%s%s"
        (make_indent indent_level)
        (ValID.to_string a)
        (match cond with Normal.IfEq -> "=" | Normal.IfLess -> "<")
        (ValID.to_string b)
        (match c.expr with Let _ | Conditional _ -> "" | _ -> (make_indent (indent_level + 1)))
        (string_of_expr ~indent_level:(indent_level + 1) c)
        (make_indent indent_level)
        (match d.expr with Let _ | Conditional _ -> "" | _ -> (make_indent (indent_level + 1)))
        (string_of_expr ~indent_level:(indent_level + 1) d)
  | Var a ->
      string_of_sp_var a
  | KnownFuncVar a ->
      (ValID.to_string a)
  | Let (a, b, c) ->
      begin match b.expr with
      | Let _ | Conditional _ ->
          sprintf "%slet %s =\n%s\n%sin\n%s%s"
            (make_indent indent_level)
            (string_of_sp_var a)
            (string_of_expr ~indent_level:(indent_level + 1) b)
            (make_indent indent_level)
            (match c.expr with | Let _ | Conditional _ -> "" | _ -> (make_indent indent_level))
            (string_of_expr ~indent_level c)
      | _ ->
          sprintf "%slet %s = %s in\n%s%s"
            (make_indent indent_level)
            (string_of_sp_var a)
            (string_of_expr ~indent_level b)
            (match c.expr with | Let _ | Conditional _ -> "" | _ -> (make_indent indent_level))
            (string_of_expr ~indent_level c)
      end
  | ApplyKnown (f, args) ->
      sprintf "apply(%s %s)" (ValID.to_string f) (String.concat " " (List.map string_of_sp_var args))
  | ApplyUnknown (f, args) ->
      sprintf "apply_unk(%s %s)" (ValID.to_string f) (String.concat " " (List.map string_of_sp_var args))


let string_of_function id (f : function_t) : string =
  match f.f_impl with
  | NativeFunc (f_args, f_body) ->
    (sprintf "(* %s *)\nlet %s %s =\n"
      f.f_name
      (ValID.to_string id)
      (String.concat " " (List.map string_of_sp_var f_args))) ^
    (string_of_expr ~indent_level:1 f_body)
  | ExtFunc (ext_impl, _) ->
    sprintf "EXTERNAL %s ==> %s\n" f.f_name ext_impl


let string_of_program (a : program_t) =
  let function_strings = VMap.fold
    (fun f_id f_def acc -> (string_of_function f_id f_def) :: acc)
    a.functions
    []
  in
  String.concat "\n\n" function_strings


let infer_sp_var v =
  match v.SPVar.storage with
  | Function.Value -> Value (ValID.of_var v)
  | Function.Ref   -> Ref   (RefID.of_var v)


let expr_id_count = ref 0

let free_expr_id () =
  let result = !expr_id_count in
  let () = incr expr_id_count in
  result


(* Find locations where a reference type is cloned, and annotate them with a cloning operation.
 * We consider a reference type to be cloned whenever a Let expression is binding to a
 * reference-type Var.
 *
 * As a side-effect, unique identifiers are attached to every subexpression in the tree. *)
let rec identify_ref_clones ?(is_binding_expr=false) (expr : Function.t) : t =
  let rt_expr =
    match expr with
    | Function.Unit                -> Unit
    | Function.Int x               -> Int x
    | Function.Conditional (cond, a, b, e1, e2) ->
        Conditional (cond, ValID.of_var a, ValID.of_var b,
          identify_ref_clones ~is_binding_expr e1,
          identify_ref_clones ~is_binding_expr e2)
    | Function.Var a ->
        if is_binding_expr then
          begin match a.SPVar.storage with 
          | Function.Value ->
              Var (infer_sp_var a)
          | Function.Ref   -> 
              let ref_clone = Function.find_ext_function_def_by_name
                (Builtins.asm_name_of_id Builtins.ref_clone)
              in
              ApplyKnown (ValID.of_var ref_clone, [Ref (RefID.of_var a)])
          end
        else
          Var (infer_sp_var a)
    | Function.KnownFuncVar a ->
        KnownFuncVar (ValID.of_var a)
    | Function.Let (a, e1, e2) ->
        Let (infer_sp_var a,
          identify_ref_clones ~is_binding_expr:true e1,
          identify_ref_clones ~is_binding_expr e2)
    | Function.ApplyKnown (f, f_args)   -> ApplyKnown (ValID.of_var f, List.map infer_sp_var f_args)
    | Function.ApplyUnknown (f, f_args) -> ApplyUnknown (ValID.of_var f, List.map infer_sp_var f_args)
  in
  {id = free_expr_id (); expr = rt_expr}


(* Identify cloning of reference types across the whole program. *)
let identify_ref_clones_program (program : Function.program_t) : program_t =
  let annot_functions =
    SPVMap.fold
      (fun f_id f_def acc ->
        let annot_f =
          match f_def.Function.f_impl with
          | Function.NativeFunc (args, body) -> {
              f_name = f_def.Function.f_name;
              f_impl = NativeFunc (List.map infer_sp_var args, identify_ref_clones body)
            }
          | Function.ExtFunc (asm_name, arg_count) -> {
              f_name = f_def.Function.f_name;
              f_impl = ExtFunc (asm_name, arg_count)
            }
        in
        VMap.add (ValID.of_var f_id) annot_f acc)
      program.Function.functions
      VMap.empty
  in {
    functions   = annot_functions;
    entry_point = ValID.of_var program.Function.entry_point
  }


module TOrd = struct
  (* Namespace collision... *)
  type top_t = t
  type t = top_t
  let compare e1 e2 = if e1.id < e2.id then -1 else if e1.id > e2.id then 1 else 0
end
module TMap = Map.Make(TOrd)


type cfn_t = {
  (* Successor nodes, if any *)
  successors : t list;
  (* Inputs for this node (reference types only) *)
  inputs : RSet.t;
  (* Outputs for this node (reference types only) *)
  outputs : RSet.t
}

type cfg_state_t = {
  (* Current expression map *)
  map : cfn_t TMap.t;
  (* Reference-type variable being bound to the current expression, if any *)
  binding : RefID.t option;
  (* Expression in which [binding] will be in scope, if any *)
  scope_expr : t option
}


let list_of_opt x = match x with Some y -> [y] | None -> []


let cfn_of_vars state expr vars =
  let inputs = List.fold_left
    (fun acc x ->
      match x with
      | Value v -> acc
      | Ref   r -> RSet.add r acc)
    RSet.empty
    vars
  in
  TMap.add expr {
    successors = list_of_opt state.scope_expr;
    inputs;
    outputs = match state.binding with Some x -> RSet.singleton x | None -> RSet.empty
  } state.map


(* Construct the control flow graph to be used for reference-type liveness analysis. *)
let rec make_control_flow_graph
  (state : cfg_state_t)
  (expr : t)
    : cfn_t TMap.t =
  match expr.expr with
  | Unit | Int _ | KnownFuncVar _ ->
      TMap.add expr {
          successors = list_of_opt state.scope_expr;
          inputs     = RSet.empty;
          outputs    = match state.binding with Some x -> RSet.singleton x | None -> RSet.empty
        } state.map
  | Conditional (cond, a, b, e1, e2) ->
      let e1_map    = make_control_flow_graph state e1 in
      let e1_e2_map = make_control_flow_graph {state with map = e1_map} e2 in
      TMap.add expr {
          successors = [e1; e2];
          inputs     = RSet.empty;
          outputs    = match state.binding with Some x -> RSet.singleton x | None -> RSet.empty
        } e1_e2_map
  | Let (a, e1, e2) ->
      (* The bound variable becomes the output of expression [e1]. *)
      let binding =
        match a with
        | Value v -> None
        | Ref   v -> Some v
      in
      let e2_map    = make_control_flow_graph state e2 in
      let e1_e2_map = make_control_flow_graph {map = e2_map; binding; scope_expr = Some e2} e1 in
      (* The let-binding node itself has only a trivial entry in the CFG; it's just a pass-through
       * to [e1].  This ensures that the inputs of [e1] and [e2] are both propagated up correctly
       * during liveness analysis. *)
      TMap.add expr {
        successors = [e1];
        inputs     = RSet.empty;
        outputs    = RSet.empty;
      } e1_e2_map
  | ApplyKnown (_, args) | ApplyUnknown (_, args) ->
      cfn_of_vars state expr args
  | Var x ->
      cfn_of_vars state expr [x]


(* Compute the identifiers for CFG nodes which may immediately follow node [expr]. *)
let cfn_successors graph expr =
  (TMap.find expr graph).successors


(* Compute the set of variables used as inputs for CFG node [expr].  (In this context, we only care
 * about reference types, so value types do not appear in the result. *)
let cfn_inputs graph expr =
  (TMap.find expr graph).inputs


(* Compute the set of variables used as outputs for CFG node [expr].  (In this context, we only
 * care about reference types, so value types do not appear in the result.) *)
let cfn_outputs graph expr =
  (TMap.find expr graph).outputs


module Cfg = struct
  type t = cfn_t TMap.t

  module Id   = TOrd
  module VSet = RSet

  let fold f graph a = TMap.fold (fun id node acc -> f id acc) graph a
  let successors = cfn_successors
  let inputs     = cfn_inputs
  let outputs    = cfn_outputs
end

module LSolver = Liveness.Make(Cfg)


(* Locate up a named external function in the list of known functions. *)
let find_ext_function_def_by_name (program : program_t) (asm_name : string) : ValID.t =
  let result =
    VMap.fold
      (fun id def result_opt ->
        match def.f_impl with
        | ExtFunc (name, _) when name = asm_name ->
            Some id
        | _ ->
            result_opt)
      program.functions
      None
  in
  match result with
  | None ->
      let () = Printf.fprintf stderr "Missing asm function: %s\n" asm_name in
      assert false
  | Some x ->
      x


let rec insert_ref_release_aux
  ?(local_refs=RSet.empty)                (* Set of references which are live in this expr *)
  ?(curr_binding=None)                    (* Variable which is bound to the current expression, if any *)
  (ref_release : ValID.t)                 (* Variable bound to external function zml_ref_release *)
  (liveness : LSolver.t LSolver.IdMap.t)  (* Reference variable liveness information *)
  (expr : t)                              (* Expression to be analyzed *)
    : t =
  (* FIXME: correct, but hacky *)
  let free_value_var () = infer_sp_var {SPVar.id = Normal.free_var(); SPVar.storage = Function.Value} in
  let free_ref_var ()   = infer_sp_var {SPVar.id = Normal.free_var(); SPVar.storage = Function.Ref} in
  let insert_release_let ref expr = {
    id = free_expr_id ();
    expr = Let (free_value_var (),
            {id = free_expr_id (); expr = ApplyKnown (ref_release, [Ref ref])}, expr)
  } in
  match expr.expr with
  | Conditional (cond, a, b, e1, e2) ->
      (* There is one corner case where we emit cleanup code associated with a conditional.  If
       * a variable is live in one branch but dead in the other branch, we immediately release the
       * variable on the branch where it is dead. *)
      let expr_live = (LSolver.IdMap.find expr liveness).LSolver.live_out in
      let branch_cleanup branch_expr =
        let live_info = LSolver.IdMap.find branch_expr liveness in
        let dead_refs = RSet.diff expr_live live_info.LSolver.live_in in
        RSet.fold
          (fun dead_ref acc -> insert_release_let dead_ref acc)
          dead_refs
          (insert_ref_release_aux ~local_refs ~curr_binding ref_release liveness branch_expr)
      in
      {expr with expr = Conditional (cond, a, b, branch_cleanup e1, branch_cleanup e2)}
  | Let (a, e1, e2) ->
      (* There is one corner case where we emit cleanup code associated with the let-binding.
       * If [a] is a reference-type binding which is never used in [e2], then we release immediately. *)
      let e2_live = LSolver.IdMap.find e2 liveness in
      let (e2_local_refs, unused_binding_opt) =
        match a with
        | Value v -> (local_refs, None)
        | Ref   r -> (RSet.add r local_refs, if RSet.mem r e2_live.LSolver.live_in then None else Some r)
      in
      let e2_with_release =
        insert_ref_release_aux ~local_refs:e2_local_refs ~curr_binding ref_release liveness e2
      in
      {expr with expr = Let (a,
        insert_ref_release_aux ~local_refs ~curr_binding:(Some a) ref_release liveness e1,
        match unused_binding_opt with
        | None   -> e2_with_release
        | Some r -> insert_release_let r e2_with_release)}
  | Unit | Int _ | Var _ | KnownFuncVar _
  | ApplyKnown _ | ApplyUnknown _ ->
      begin match curr_binding with
      | Some binding ->
        let expr_live = LSolver.IdMap.find expr liveness in
        let dead_refs = RSet.diff expr_live.LSolver.live_in expr_live.LSolver.live_out in
        let dead_local_refs = RSet.inter local_refs dead_refs in
        if RSet.is_empty dead_local_refs then
          expr
        else
          let new_bind_var =
            match binding with
            | Value _ -> free_value_var ()
            | Ref _   -> free_ref_var ()
          in {
            id = free_expr_id ();
            expr = Let (new_bind_var, expr,
              RSet.fold
                (fun dead_ref acc -> insert_release_let dead_ref acc)
                dead_local_refs
                {id = free_expr_id (); expr = Var new_bind_var})
          }
      | None ->
          (* Not an intermediate expression *)
          expr
      end


(* Insert zml_ref_release operations for expression [expr], using the [liveness] map.
 * References are released under the following conditions:
 *    1) the reference is created within the body of [expr]
 *    2) the reference is an intermediate value, not the final value of the [expr] *)
let insert_ref_release (program : program_t) (expr : t) : t =
  let cfg_init_state = {
    map        = TMap.empty;
    binding    = None;
    scope_expr = None
  } in
  let cfg = make_control_flow_graph cfg_init_state expr in
  let liveness = LSolver.solve cfg in
  let ref_release = find_ext_function_def_by_name program
    (Builtins.asm_name_of_id Builtins.ref_release)
  in
  insert_ref_release_aux ref_release liveness expr


(* Rewrite the [program] inserting code for automatic management of reference lifetimes. *)
let insert_ref_management (program : Function.program_t) : program_t =
  let clone_annot_prog = identify_ref_clones_program program in
  let release_annot_func = VMap.fold
    (fun f_id f acc ->
      let impl =
        match f.f_impl with
        | NativeFunc (args, expr) ->
            NativeFunc (args, insert_ref_release clone_annot_prog expr)
        | ExtFunc _ ->
            f.f_impl
      in
      VMap.add f_id {f with f_impl = impl} acc)
    clone_annot_prog.functions
    VMap.empty
  in { clone_annot_prog with
    functions = release_annot_func;
  }


