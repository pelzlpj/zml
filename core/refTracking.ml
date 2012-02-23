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

open Printf

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
  val to_string : t -> string
end

(* Opaque identifier for value-type variables *)
module ValID : OPAQUE_ID = struct
  type t = int
  let compare a b = if a < b then -1 else if a > b then 1 else 0
  let of_var x = match x.SPVar.storage with Function.Value -> x.SPVar.id | Function.Ref -> assert false
  let to_string x = sprintf "vv%d" x
end

(* Opaque identifier for reference-type variables *)
module RefID : OPAQUE_ID = struct
  type t = int
  let compare a b = if a < b then -1 else if a > b then 1 else 0
  let of_var x = match x.SPVar.storage with Function.Ref -> x.SPVar.id | Function.Value -> assert false
  let to_string x = sprintf "rv%d" x
end

module RSet = Set.Make(RefID)

(* Opaque identifier for variables with arbitrary storage policy *)
type sp_var_t =
  | Value of ValID.t
  | Ref   of RefID.t

let string_of_sp_var x = match x with Value v -> ValID.to_string v | Ref r -> RefID.to_string r

module VMap = Map.Make(ValID)


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
  | ApplyUnknown of ValID.t * (sp_var_t list)   (* Application of an "unknown" function (computed address) *)
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
      sprintf "(%s %s %s)"  (ValID.to_string a) op_s (ValID.to_string b)
  | UnaryOp (Normal.Neg, a) -> sprintf "(- %s)" (ValID.to_string a)
  | Conditional (cond, a, b, c, d) ->
      sprintf "%sif %s %s %s then\n%s%s\n%selse\n%s%s"
        (make_indent indent_level)
        (ValID.to_string a)
        (match cond with Normal.IfEq -> "=" | Normal.IfLess -> "<")
        (ValID.to_string b)
        (match c with Let _ | Conditional _ -> "" | _ -> (make_indent (indent_level + 1)))
        (string_of_expr ~indent_level:(indent_level + 1) c)
        (make_indent indent_level)
        (match d with Let _ | Conditional _ -> "" | _ -> (make_indent (indent_level + 1)))
        (string_of_expr ~indent_level:(indent_level + 1) d)
  | Var a ->
      string_of_sp_var a
  | Let (a, b, c) ->
      begin match b with
      | Let _ | Conditional _ ->
          sprintf "%slet %s =\n%s\n%sin\n%s%s"
            (make_indent indent_level)
            (string_of_sp_var a)
            (string_of_expr ~indent_level:(indent_level + 1) b)
            (make_indent indent_level)
            (match c with | Let _ | Conditional _ -> "" | _ -> (make_indent indent_level))
            (string_of_expr ~indent_level c)
      | _ ->
          sprintf "%slet %s = %s in\n%s%s"
            (make_indent indent_level)
            (string_of_sp_var a)
            (string_of_expr ~indent_level b)
            (match c with | Let _ | Conditional _ -> "" | _ -> (make_indent indent_level))
            (string_of_expr ~indent_level c)
      end
  | ApplyKnown (f, args) ->
      sprintf "apply(%s %s)" (ValID.to_string f) (String.concat " " (List.map string_of_sp_var args))
  | ApplyUnknown (f, args) ->
      sprintf "apply_unk(%s %s)" (ValID.to_string f) (String.concat " " (List.map string_of_sp_var args))
  | ArrayAlloc (a, b) ->
      sprintf "array_alloc(%s, %s)" (ValID.to_string a) (string_of_sp_var b)
  | ArraySet (a, b, c) ->
      sprintf "array_set(%s, %s, %s)" (RefID.to_string a) (ValID.to_string b) (string_of_sp_var c)
  | ArrayGet (a, b) ->
      sprintf "array_get(%s, %s)" (RefID.to_string a) (ValID.to_string b)
  | RefClone r ->
      sprintf "clone(%s)" (RefID.to_string r)
  | RefRelease r ->
      sprintf "release(%s)" (RefID.to_string r)


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
  | Function.ApplyUnknown (f, f_args) -> ApplyUnknown (ValID.of_var f, List.map infer_sp_var f_args)
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
      (* The bound variable becomes the output of expression [e1]. *)
      let binding =
        match a with
        | Value v -> None
        | Ref   v -> Some v
      in
      let e2_map    = make_control_flow_graph state e2 in
      let e1_e2_map = make_control_flow_graph {map = e2_map; binding; scope_expr = Some e2} e1 in
      (* The current node has only a trivial entry in the CFG; it's just there to allow the output
       * of [e1] to flow through to [e2]. *)
      TMap.add expr {
        successor = Some e2;
        inputs    = RSet.empty;
        outputs   = RSet.empty;
      } e1_e2_map
  | ApplyKnown (_, args) | ApplyUnknown (_, args) ->
      cfn_of_vars state expr args
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
  ?(local_refs=RSet.empty)                (* Set of references which are live in this expr *)
  ?(curr_binding=None)                    (* Variable which is bound to the current expression, if any *)
  (liveness : LSolver.t LSolver.IdMap.t)  (* Reference variable liveness information *)
  (expr : t)                              (* Expression to be analyzed *)
    : t =
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
        if RSet.is_empty dead_local_refs then
          expr
        else
          Let (new_bind_var, expr,
            RSet.fold
              (fun dead_ref acc ->
                Let (free_value_var (), RefRelease dead_ref, acc))
              dead_local_refs
              (Var new_bind_var))
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
  let release_annot_func = VMap.fold
    (fun f_id f acc ->
      let impl =
        match f.f_impl with
        | NativeFunc (args, expr) ->
            NativeFunc (args, insert_ref_release expr)
        | ExtFunc _ ->
            f.f_impl
      in
      VMap.add f_id {f with f_impl = impl} acc)
    clone_annot_prog.functions
    VMap.empty
  in { clone_annot_prog with
    functions = release_annot_func;
  }


