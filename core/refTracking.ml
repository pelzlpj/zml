(* Management of variable lifetimes for reference types.
 *
 * ZML's initial target is the Z-Machine, which is a pretty weird VM.  Of particular
 * note: the function call stack is largely inaccessible, which makes it impossible to
 * scan the stack for GC roots.  The workaround is to track reference types explicitly.
 *
 * To this end, the ZML runtime registers references in a global roots table whenever
 * a new reference is created (allocating an array, retrieving a reference from an
 * array-of-references, etc.).  The code which calls into the runtime must explicitly
 * release these references when they fall out of scope.
 *
 * This module examines the code emitted by [Function.extract_functions], and inserts
 * the code necessary to release references.  Liveness analysis is performed in
 * order to release references as early as possible.
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


module SPVar  = Function.SPVar
module SPVMap = Function.SPVMap
module SPVSet = Set.Make(SPVar)
type binary_op_t = Function.binary_op_t
type unary_op_t  = Function.unary_op_t
type cond_t      = Function.conditional_t


module type OPAQUE_ID = sig
  type t
  val compare : t -> t -> int
  val of_var : SPVar.t -> t
end

(* Opaque identifier for value-type variables *)
module ValID : OPAQUE_ID = struct
  type t = int
  let compare a b = if a < b then -1 else if a > b then 1 else 0
  let of_var x = match x.SPVar.storage with Function.Value -> x.SPVar.id | Function.Ref -> assert false
end

(* Opaque identifier for reference-type variables *)
module RefID : OPAQUE_ID = struct
  type t = int
  let compare a b = if a < b then -1 else if a > b then 1 else 0
  let of_var x = match x.SPVar.storage with Function.Ref -> x.SPVar.id | Function.Value -> assert false
end

module RSet = Set.Make(RefID)

(* Opaque identifier for variables with arbitrary storage policy *)
type sp_var_t =
  | Value of ValID.t
  | Ref   of RefID.t


type t =
  | Unit                                        (* Unit literal *)
  | Int of int                                  (* Integer constant *)
  | BinaryOp of binary_op_t * ValID.t * ValID.t (* Binary integer operation *)
  | UnaryOp of unary_op_t * ValID.t             (* Unary integer operation *)
  | Conditional of cond_t * ValID.t * ValID.t
      * t * t                                   (* Conditional form *)
  | Var of sp_var_t                             (* Bound variable reference *)
  | Let of sp_var_t * t * t                     (* Let binding for a variable *)
  | ApplyKnown of ValID.t * (sp_var_t list)     (* Application of "known" function *)
  | ApplyUnknown of RefID.t * (sp_var_t list)   (* Application of an "unknown" function (computed address) *)
  | ArrayAlloc of ValID.t * sp_var_t            (* Construct a new array (size, init) *)
  | ArraySet of RefID.t * ValID.t * sp_var_t    (* Store a ref or value in an array (arr, index, ref) *)
  | ArrayGet of RefID.t * ValID.t               (* Get a ref or value from an array (arr, index) *)
  | RefClone of RefID.t                         (* Create new references which points to same object *)
  | RefRelease of RefID.t                       (* Release a reference *)


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
  functions   : function_t SPVMap.t;
  (* Function to be invoked as program entry point (with type "unit -> unit") *)
  entry_point : SPVar.t
}

let infer_sp_var v =
  match v.SPVar.storage with
  | Function.Value -> Value (ValID.of_var v)
  | Function.Ref   -> Ref   (RefID.of_var v)


(* Find locations where a reference type is cloned, and annotate them with a cloning operation.
 * We consider a reference type to be cloned whenever a Let expression is binding to a
 * reference-type Var.  *)
let rec identify_ref_clones ?(is_binding_expr=false) (expr : Function.t) : t =
  match expr with
  | Function.Unit                -> Unit
  | Function.Int x               -> Int x
  | Function.BinaryOp (op, a, b) -> BinaryOp (op, ValID.of_var a, ValID.of_var b)
  | Function.UnaryOp (op, a)     -> UnaryOp (op, ValID.of_var a)
  | Function.Conditional (cond, a, b, e1, e2) ->
      Conditional (cond, ValID.of_var a, ValID.of_var b,
        identify_ref_clones ~is_binding_expr e1,
        identify_ref_clones ~is_binding_expr e2)
  | Function.Var a ->
      if is_binding_expr then
        begin match a.SPVar.storage with 
        | Function.Value -> Var (infer_sp_var a)
        | Function.Ref   -> RefClone (RefID.of_var a)
        end
      else
        Var (infer_sp_var a)
  | Function.Let (a, e1, e2) ->
      Let (infer_sp_var a,
        identify_ref_clones ~is_binding_expr:true e1,
        identify_ref_clones ~is_binding_expr e2)
  | Function.ApplyKnown (f, f_args)   -> ApplyKnown (ValID.of_var f, List.map infer_sp_var f_args)
  | Function.ApplyUnknown (f, f_args) -> ApplyUnknown (RefID.of_var f, List.map infer_sp_var f_args)
  | Function.ArrayAlloc (size, init)  -> ArrayAlloc (ValID.of_var size, infer_sp_var init)
  | Function.ArraySet (arr, index, v) -> ArraySet (RefID.of_var arr, ValID.of_var index, infer_sp_var v)
  | Function.ArrayGet (arr, index)    -> ArrayGet (RefID.of_var arr, ValID.of_var index)


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
        SPVMap.add f_id annot_f acc)
      program.Function.functions
      SPVMap.empty
  in {
    functions   = annot_functions;
    entry_point = program.Function.entry_point
  }


module TOrd = struct
  type top_t = t
  type t = top_t
  let compare = Pervasives.compare
end
module TMap = Map.Make(TOrd)


type cfn_t = {
  (* Successor node, if any *)
  successor : t option;
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
    successor = state.scope_expr;
    inputs;
    outputs = match state.binding with Some x -> RSet.singleton x | None -> RSet.empty
  } state.map


(* Construct the control flow graph to be used for reference-type liveness analysis. *)
let rec make_control_flow_graph
  (state : cfg_state_t)
  (expr : t)
    : cfn_t TMap.t =
  match expr with
  | Unit | Int _ | BinaryOp _ | UnaryOp _ ->
      TMap.add expr {
          successor = state.scope_expr;
          inputs    = RSet.empty;
          outputs   = match state.binding with Some x -> RSet.singleton x | None -> RSet.empty
        } state.map
  | Conditional (cond, a, b, e1, e2) ->
      let e1_map    = make_control_flow_graph state e1 in
      let e1_e2_map = make_control_flow_graph {state with map = e1_map} e2 in
      TMap.add expr {
          successor = state.scope_expr;
          inputs    = RSet.empty;
          outputs   = match state.binding with Some x -> RSet.singleton x | None -> RSet.empty
        } e1_e2_map
  | Let (a, e1, e2) ->
      (* Note: the let-expression itself receives no node in the CFG.  Instead, the
       * bound variable becomes the output of expression [e1]. *)
      let binding =
        match a with
        | Value v -> None
        | Ref   v -> Some v
      in
      let e2_map = make_control_flow_graph state e2 in
      make_control_flow_graph {
          map = e2_map;
          binding;
          scope_expr = Some e2
        } e1
  | ApplyKnown (_, args) ->
      cfn_of_vars state expr args
  | ApplyUnknown (f, args) ->
      cfn_of_vars state expr ((Ref f) :: args)
  | ArrayAlloc (_, x) | Var x ->
      cfn_of_vars state expr [x]
  | ArraySet (arr, _, x) ->
      cfn_of_vars state expr ((Ref arr) :: [x])
  | ArrayGet (r, _) | RefClone r | RefRelease r ->
      cfn_of_vars state expr [Ref r]


(* Compute the identifiers for CFG nodes which may immediately follow node [expr]. *)
let cfn_successors graph expr =
  match (TMap.find expr graph).successor with
  | None   -> []
  | Some e -> [e]


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


let rec insert_ref_release_aux
  ?(local_refs=RSet.empty)
  ?(curr_binding=None)
  (liveness : LSolver.t LSolver.IdMap.t)
  (expr : t)
    =
  (* FIXME: correct, but hacky *)
  let free_value_var () = infer_sp_var {SPVar.id = Normal.free_var(); SPVar.storage = Function.Value} in
  let free_ref_var ()   = infer_sp_var {SPVar.id = Normal.free_var(); SPVar.storage = Function.Ref} in
  match expr with
  | Conditional (cond, a, b, e1, e2) ->
      Conditional (cond, a, b,
        insert_ref_release_aux ~local_refs ~curr_binding liveness e1,
        insert_ref_release_aux ~local_refs ~curr_binding liveness e2)
  | Let (a, e1, e2) ->
      let e2_local_refs =
        match a with
        | Value v -> local_refs
        | Ref   r -> RSet.add r local_refs
      in
      Let (a,
        insert_ref_release_aux ~local_refs ~curr_binding:(Some a) liveness e1,
        insert_ref_release_aux ~local_refs:e2_local_refs ~curr_binding liveness e2)
  | Unit | Int _ | BinaryOp _ | UnaryOp _ | Var _
  | ApplyKnown _ | ApplyUnknown _ | ArrayAlloc _
  | ArraySet _ | ArrayGet _ | RefClone _ | RefRelease _ ->
      begin match curr_binding with
      | Some binding ->
        let new_bind_var =
          match binding with
          | Value _ -> free_value_var ()
          | Ref _   -> free_ref_var ()
        in
        let expr_live = LSolver.IdMap.find expr liveness in
        let dead_local_refs = RSet.inter local_refs
          (RSet.diff expr_live.LSolver.live_in expr_live.LSolver.live_out)
        in
        Let (new_bind_var, expr,
          RSet.fold
            (fun dead_ref acc ->
              Let (free_value_var (), RefRelease dead_ref, acc))
            dead_local_refs
            (Var binding))
      | None ->
          (* Not an intermediate expression *)
          expr
      end


(* Insert RefRelease operations for expression [expr], using the [liveness] map.
 * References are released under the following conditions:
 *    1) the reference is created within the body of [expr]
 *    2) the reference is an intermediate value, not the final value of the [expr] *)
let insert_ref_release (expr : t) : t =
  let cfg_init_state = {
    map        = TMap.empty;
    binding    = None;
    scope_expr = None
  } in
  let cfg = make_control_flow_graph cfg_init_state expr in
  let liveness = LSolver.solve cfg in
  insert_ref_release_aux liveness expr


(* Rewrite the [program] inserting code for automatic management of reference lifetimes. *)
let insert_ref_management (program : Function.program_t) : program_t =
  let clone_annot_prog = identify_ref_clones_program program in
  let release_annot_func = SPVMap.fold
    (fun f_id f acc ->
      let impl =
        match f.f_impl with
        | NativeFunc (args, expr) ->
            NativeFunc (args, insert_ref_release expr)
        | ExtFunc _ ->
            f.f_impl
      in
      SPVMap.add f_id {f with f_impl = impl} acc)
    clone_annot_prog.functions
    SPVMap.empty
  in { clone_annot_prog with
    functions = release_annot_func;
  }


