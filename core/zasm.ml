
open Printf

module VarID = Normal.VarID
module VMap  = Normal.VMap
module VSet  = Normal.VSet
type var_t   = Normal.var_t

let vset_of_list = List.fold_left (fun acc x -> VSet.add x acc) VSet.empty


(* Identifiers for Z-Machine variables *)
type reg_t   = int

(* Identifiers for labels placed within a function body *)
type label_t = int

(* Some useful properties of Z-Machine assembly *)
let call_vs2_max_args    = 7
let local_variable_count = 14   (* excluding 'sp' *)


(* Construct an assembly function identifier from a function ID. *)
let asm_fun_name_of_id (program : Function.t) (f_id : var_t) =
  let f_def = VMap.find f_id program.Function.functions in
  let short_name = f_def.Function.f_name in
  if f_id = program.Function.entry_point then
    short_name
  else
    match f_def.Function.f_impl with
    | Function.NativeFunc _ ->
      sprintf "%s_%s" short_name (VarID.to_int_string f_id)
    | Function.ExtFunc ext_impl ->
      ext_impl


(* Most opcodes accept either variable identifiers (v0-v255) or integer constants
 * as operands. *)
type operand_t =
  | Reg of reg_t
  | Const of int


(* Different methods of referring to a routine to be called. *)
type routine_t =
  | Mapped of var_t   (* Typical method: looking up a function by its internal ZML id *)
  | AsmName of string (* Directly injecting the name of an assembly routine *)


(* We need only a small subset of Z-machine opcodes in order to implement
 * [Function.expr_t].  In the future, it may prove useful to use additional
 * opcodes to handle special cases.  It probably won't matter for performance,
 * but the code size could be reduced by using more compact instructions. *)
type t =
  | ADD of operand_t * operand_t * reg_t
  | SUB of operand_t * operand_t * reg_t
  | MUL of operand_t * operand_t * reg_t
  | DIV of operand_t * operand_t * reg_t
  | MOD of operand_t * operand_t * reg_t
  | JE of  operand_t * operand_t * label_t
  | JL of  operand_t * operand_t * label_t
  | JUMP of label_t
  | LOAD of reg_t * reg_t
  | STORE of reg_t * operand_t
  | CALL_VS2 of routine_t * (operand_t list) * reg_t
  | RET of operand_t
  | Label of label_t


type state_t = {
  reg_of_var : int VMap.t;    (* Maps Normal.t variables to Z-Machine registers *)
  reg_count  : int;           (* Number of registers consumed *)
  label_count: int            (* Number of labels emitted *)
}

let rec compile_virtual_aux
  (state : state_t)           (* Compilation context *)
  (result_reg)                (* Register which should be used to store the result *)
  (expr : Function.expr_t)    (* Expression to be compiled *)
    : (
      state_t *   (* New context *)
      t list      (* List of instructions for the expression *)
    ) =
  match expr with
  | Function.Unit ->
      (* For now we're treating unit as integer zero.  It shouldn't matter. *)
      compile_virtual_aux state result_reg (Function.Int 0)
  | Function.Int i ->
      (state, [STORE (result_reg, Const i)])
  | Function.Add (a, b) ->
      compile_virtual_binary_int state result_reg (fun x y z -> ADD (x, y, z)) a b
  | Function.Sub (a, b) ->
      compile_virtual_binary_int state result_reg (fun x y z -> SUB (x, y, z)) a b
  | Function.Mul (a, b) ->
      compile_virtual_binary_int state result_reg (fun x y z -> MUL (x, y, z)) a b
  | Function.Div (a, b) ->
      compile_virtual_binary_int state result_reg (fun x y z -> DIV (x, y, z)) a b
  | Function.Mod (a, b) ->
      compile_virtual_binary_int state result_reg (fun x y z -> MOD (x, y, z)) a b
  | Function.Neg a ->
      (* Negation is implemented as subtraction from zero. *)
      (state, [SUB (Const 0, Reg (VMap.find a state.reg_of_var), result_reg)])
  | Function.IfEq (a, b, e1, e2) ->
      compile_virtual_if state result_reg true a b e1 e2
  | Function.IfLess (a, b, e1, e2) ->
      compile_virtual_if state result_reg false a b e1 e2
  | Function.Var a ->
      (state, [LOAD (VMap.find a state.reg_of_var, result_reg)])
  | Function.Let (a, e1, e2) ->
      (* "let" just leads to emitting instructions for [e1] prior to [e2],
       * with the additional constraint that [a] becomes an alias for the
       * [e1] result register while compiling [e2]. *)
      let head_result_reg = state.reg_count in
      let state = {state with reg_count = head_result_reg + 1} in
      let (state, head_asm) = compile_virtual_aux state head_result_reg e1 in
      let new_binding_state = {state with reg_of_var = VMap.add a head_result_reg state.reg_of_var} in
      let (state, tail_asm) = compile_virtual_aux new_binding_state result_reg e2 in
      (state, head_asm @ tail_asm)
  | Function.Apply (g, g_args) ->
      let arg_regs = List.map (fun v -> Reg (VMap.find v state.reg_of_var)) g_args in
      (state, [CALL_VS2 (Mapped g, arg_regs, result_reg)])

(* Compile a binary integer operation. *)
and compile_virtual_binary_int state result_reg f a b = (
  state,
  [f (Reg (VMap.find a state.reg_of_var)) (Reg (VMap.find b state.reg_of_var)) result_reg]
)

(* Compile an IfEq or IfLess form. *)
and compile_virtual_if state result_reg is_cmp_equality a b e1 e2 =
  (* Compiles down to assembly of this form:
   *    je a b ?true_label
   *    (code for e2)
   *    jump ?exit_label
   * true_label:
   *    (code_for_e1)
   * exit_label:
   *)    
  let (state, true_branch)  = compile_virtual_aux state result_reg e1 in
  let (state, false_branch) = compile_virtual_aux state result_reg e2 in
  let true_label = state.label_count in
  let exit_label = true_label + 1 in
  let branch_inst =
    let a_reg = Reg (VMap.find a state.reg_of_var) in
    let b_reg = Reg (VMap.find b state.reg_of_var) in
    if is_cmp_equality then
      [JE (a_reg, b_reg, true_label)]
    else
      [JL (a_reg, b_reg, true_label)]
  in (
    {state with label_count = exit_label + 1},
    (branch_inst @
      false_branch @
      [JUMP exit_label; Label true_label] @
      true_branch @ 
      [Label exit_label])
  )


(* Compile a function to "virtual" Z5 assembly.  This is Z-machine assembly
 * with an infinite number of registers (aka "local variables") available. *)
let compile_virtual
  (f_args : var_t list)         (* Function arguments *)
  (f_body : Function.expr_t)    (* Function body *)
    : (reg_t list) *            (* Virtual registers assigned to function arguments *)
      (t list) *                (* Generated virtual assembly *)
      int =                     (* Count of virtual registers used (0 to N-1) *)
  (* call_vs2 supports 0 through 7 arguments.  Implementing functions with
   * more than seven arguments will require heap-allocating a reference array
   * as storage for the extra args. *)
  let () = assert (List.length f_args <= call_vs2_max_args) in
  let result_reg = 0 in
  let init_state = List.fold_left
    (fun acc arg -> {acc with
       reg_of_var = VMap.add arg acc.reg_count acc.reg_of_var;
       reg_count  = acc.reg_count + 1
      })
    {reg_of_var = VMap.empty; reg_count = result_reg + 1; label_count = 0}
    f_args
  in
  let (state, assembly) = compile_virtual_aux init_state result_reg f_body in
  (List.map (fun x -> VMap.find x state.reg_of_var) f_args,
    assembly @ [RET (Reg result_reg)],
    state.reg_count)



(* Node of a control flow graph. *)
type cfg_node_t = {
  instruction : t;            (* Instruction under consideration *)
  successors  : int list;     (* Offsets of instructions which may follow this one *)
  gen         : VSet.t;       (* Set of variables which are read by the instruction *)
  kill        : VSet.t;       (* Set of variables which are written by the instruction *)
  live_in     : VSet.t;       (* Set of variables which are live immediately before this instruction *)
  live_out    : VSet.t        (* Set of variables which are live immediately after this instruction *)
}


module Label = struct
  type t = label_t
  let compare e1 e2 = if e1 < e2 then -1 else if e1 > e2 then 1 else 0
end
module LMap = Map.Make(Label)

(* Generate a lookup table for the offsets at which labels are found in
 * an assembly fragment. *)
let make_label_map asm : int LMap.t =
  let (_, result) =
    List.fold_left
      (fun (i, m) inst ->
        match inst with
        | Label label ->
            let () = assert (not (LMap.mem label m)) in
            (i + 1, LMap.add label i m)
        | _ ->
            (i + 1, m))
      (0, LMap.empty)
      asm
  in
  result


module Int = struct
  type t = int
  let compare e1 e2 = if e1 < e2 then -1 else if e1 > e2 then 1 else 0
end
module IMap = Map.Make(Int)


(* Initialize a single node of the control flow graph. *)
let init_control_flow_node
    (cfg_len : int)               (* Total number of nodes in the control flow graph *)
    (label_offsets : int LMap.t)  (* Lookup table for mapping labels to node numbers *)
    (i : int)                     (* Index of this node *)
    (inst : t)                    (* Instruction for this node *)
      : cfg_node_t =
  let default_node = {
    instruction = inst;
    successors  = if i < cfg_len then [i + 1] else [];
    gen         = VSet.empty;
    kill        = VSet.empty;
    live_in     = VSet.empty;
    live_out    = VSet.empty
  } in
  match inst with
  | ADD (op1, op2, v3) | SUB (op1, op2, v3) | MUL (op1, op2, v3)
  | DIV (op1, op2, v3) | MOD (op1, op2, v3) ->
      let binary_op_node = { default_node with kill = VSet.singleton v3 } in
      begin match (op1, op2) with
      | (Reg v1, Reg v2) ->
          { binary_op_node with gen = vset_of_list [v1; v2] }
      | (Reg v1, Const _) | (Const _, Reg v1) ->
          { binary_op_node with gen = VSet.singleton v1 }
      | (Const _, Const _) ->
          binary_op_node
      end
  | JE (op1, op2, label) | JL (op1, op2, label) ->
      let branch_node = { default_node with
        instruction = inst;
        successors  = (LMap.find label label_offsets) :: default_node.successors
      } in
      begin match (op1, op2) with
      | (Reg v1, Reg v2) ->
          { branch_node with gen = vset_of_list [v1; v2] }
      | (Reg v1, Const _) | (Const _, Reg v1) ->
          { branch_node with gen = VSet.singleton v1 }
      | (Const _, Const _) ->
          branch_node
      end
  | JUMP label -> { default_node with
      successors = [LMap.find label label_offsets];
    }
  | LOAD (v1, v2) -> { default_node with
      gen  = VSet.singleton v1;
      kill = VSet.singleton v2
    }
  | STORE (v1, op2) ->
      let store_node = { default_node with kill = VSet.singleton v1 } in
      begin match op2 with
      | Reg v2 -> { store_node with gen = VSet.singleton v2 }
      | Const _ -> store_node
      end
  | CALL_VS2 (f_id, args, result) ->
      List.fold_left
        (fun acc arg ->
          match arg with
          | Reg v   -> { acc with gen = VSet.add v acc.gen }
          | Const _ -> acc)
        { default_node with kill = VSet.singleton result }
        args
  | RET op ->
      let return_node = { default_node with successors = [] } in
      begin match op with
      | Reg v   -> { return_node with gen = VSet.singleton v }
      | Const _ -> return_node
      end
  | Label _ ->
      default_node


(* Initialize the control flow graph, in preparation for iterative solution. *)
let init_control_flow_graph (asm : t list) : cfg_node_t IMap.t =
  let cfg_len = List.length asm in
  let label_offsets = make_label_map asm in
  let (_, graph) = List.fold_left
    (fun (i, m) inst ->
      let node = init_control_flow_node cfg_len label_offsets i inst in
      (i + 1, IMap.add i node m))
    (0, IMap.empty)
    asm
  in
  graph


(* Solve for the sets of variables which are "live" before and after every instruction. *)
let solve_liveness (asm : t list) : cfg_node_t IMap.t =
  let rec fixpoint graph =
    let next_graph = IMap.fold
      (fun i old_node acc ->
        let outputs_not_killed = VSet.diff old_node.live_out old_node.kill in
        let successor_inputs = List.fold_left
          (fun acc j -> VSet.union acc (IMap.find j graph).live_in)
          VSet.empty
          old_node.successors
        in
        let new_node = { old_node with
          live_in  = VSet.union old_node.gen outputs_not_killed;
          live_out = successor_inputs
        } in
        IMap.add i new_node acc)
      graph
      IMap.empty
    in
    if next_graph = graph then graph else fixpoint next_graph
  in
  fixpoint (init_control_flow_graph asm)


(* As VSet.fold, but iterating over elements of the product of the two sets. *)
let vset_fold_product f s1 s2 init =
  VSet.fold
    (fun s1_x s1_acc ->
      VSet.fold
        (fun s2_x s2_acc -> f s1_x s2_x s2_acc)
        s2
        s1_acc)
    s1
    init


let vset_map f s =
  VSet.fold
    (fun x acc -> VSet.add (f x) acc) 
    s
    VSet.empty


let vmap_naive_union m1 m2 =
  VMap.merge
    (fun key m1_val_opt m2_val_opt ->
      match (m1_val_opt, m2_val_opt) with
      | (Some m1_val, Some m2_val) ->
          Some (VSet.union m1_val m2_val)
      | (Some v, None) | (None, Some v) ->
          Some v
      | (None, None) ->
          None)
    m1
    m2


exception Found_first of var_t

(* Finds the first element in the collection which satisfies the
 * predicate, if any. *)
let vmap_find_first (p : var_t -> 'a -> bool) (m : 'a VMap.t) : var_t option =
  try
    let () = VMap.iter
      (fun x y ->
        if p x y then
          raise (Found_first x)
        else
          ())
      m
    in
    None
  with Found_first x ->
    Some x
  

(* Generate an interference graph for the assembly.  The resulting data
 * structure maps each variable to a set of variables with which it interferes. *)
let make_interference_graph (asm : t list) : VSet.t VMap.t =
  let liveness = solve_liveness asm in
  (* Variable [x] interferes with [y] if [x] <> [y] and there is an
   * instruction such that x \in kill and y \in live_out. *)
  let interfering_of_instruction inst_node =
    vset_fold_product
      (fun kill_item out_item acc ->
        if kill_item = out_item then
          acc
        else
          (* Creating mappings in both directions... *)
          let kill_mapping =
            let old_kill_binding = try VMap.find kill_item acc with Not_found -> VSet.empty in
            VMap.add kill_item (VSet.add out_item old_kill_binding) acc
          in
          let old_out_binding = try VMap.find out_item kill_mapping with Not_found -> VSet.empty in
          VMap.add out_item (VSet.add kill_item old_out_binding) kill_mapping)
      inst_node.kill
      inst_node.live_out
      VMap.empty
  in
  (* All variables should be present in the graph, regardless of whether they interfere with
   * other variables.  So start with a graph containing only vertices (no edges). *)
  let all_variables = IMap.fold
    (fun _ node acc -> VSet.union (VSet.union acc node.gen) node.kill)
    liveness
    VSet.empty
  in
  let graph_with_vertices = VSet.fold
    (fun x acc -> VMap.add x VSet.empty acc)
    all_variables
    VMap.empty
  in
  IMap.fold
    (fun _ node acc -> vmap_naive_union acc (interfering_of_instruction node))
    liveness
    graph_with_vertices


let print_interference_graph graph =
  VMap.iter
    (fun var connected ->
      let connected_s = String.concat ", "
        (List.rev (VSet.fold (fun x acc -> (sprintf "%d" x) :: acc) connected []))
      in
      printf "%d: %s\n" var connected_s)
    graph



(* See Python range() builtin. *)
let list_range ?(start=0) ?(step=1) stop =
  if step = 0 then
    invalid_arg "list_range: step must be nonzero"
  else
    let rec loop acc i =
      if (step > 0 && i >= stop) || (step < 0 && i <= stop) then
        List.rev acc
      else
        loop (i :: acc) (i + step)
    in
    loop [] start



type coloring_t =
  | Colored of reg_t VMap.t   (* Successful coloring, with the map from variables to registers *)
  | Spilled of VSet.t         (* Coloring failed; one or more registers were spilled *)


(* Select colors for the nodes removed by [simplify_color_graph]. *)
let rec assign_colors
  ~(color_count : int)                (* Count of colors/registers available *)
  ~(color_map : reg_t VMap.t)         (* Accumulator for the resulting register allocation *)
  ~(spilled : VSet.t)                 (* Accumulator for spilled nodes *)
  ~(removed : (var_t * VSet.t) list)  (* Stack of nodes to be processed *)
    : coloring_t =
  let all_colors = vset_of_list (list_range color_count) in
  match removed with
  | [] ->
      if VSet.cardinal spilled > 0 then
        Spilled spilled
      else
        Colored color_map
  | (x, connected_nodes) :: tail ->
      let connected_unspilled_nodes = VSet.diff connected_nodes spilled in
      (* Due to use of [removed] as a stack, the [connected_nodes] will
       * always have been colored on a previous iteration.  So the [find]
       * never fails. *)
      let connected_colors = vset_map (fun x -> VMap.find x color_map) connected_unspilled_nodes in
      let avail_colors = VSet.diff all_colors connected_colors in
      if VSet.cardinal avail_colors > 0 then
        let color_map = VMap.add x (VSet.choose avail_colors) color_map in
        assign_colors ~color_count ~color_map ~spilled ~removed:tail
      else
        (* Coloring failure.  Spill this node and continue. *)
        assign_colors ~color_count ~color_map ~spilled:(VSet.add x spilled) ~removed:tail


(* Remove a node, and all connected edges, from the graph. *)
let remove_graph_node x g =
  let connected_nodes = VMap.find x g in
  let purged_graph =
    VSet.fold
      (fun connected_node acc ->
        let connected_node_connections = VMap.find connected_node acc in
        VMap.add connected_node (VSet.remove x connected_node_connections) acc)
      connected_nodes
      (VMap.remove x g)
  in
  (connected_nodes, purged_graph)


(* Simplify a color graph by removing nodes.  First we remove nodes with fewer
 * than [color_count] colors, then we optimistically remove the other nodes.
 * As an exception, the function args are *not* removed from the graph.
 * We "precolor" them in place to reflect the Z-machine argument passing convention. *)
let rec simplify_color_graph args color_count removed g =
  match vmap_find_first
    (fun x connected -> (not (List.mem x args)) && VSet.cardinal connected < color_count)
    g
  with
  | Some x ->
      (* Found a non-argument node with fewer than [color_count] connections. *)
      let (connected_nodes, purged_graph) = remove_graph_node x g in
      simplify_color_graph args color_count ((x, connected_nodes) :: removed) purged_graph
  | None ->
      (* Failed to find a non-argument node with fewer than [color_count] connections.  Relax the
       * restriction; check for non-argument nodes without regard for number of connections. *)
      begin match vmap_find_first
        (fun x _ -> not (List.mem x args))
        g
      with
      | Some x ->
          let (connected_nodes, purged_graph) = remove_graph_node x g in
          simplify_color_graph args color_count ((x, connected_nodes) :: removed) purged_graph
      | None ->
          removed
      end


(* Attempt to assign colors to the nodes of the [graph]. *)
let color_graph args color_count graph =
  let removed = simplify_color_graph args color_count [] graph in
  (* The only nodes remaining in the simplified graph are the argument-passing nodes.
   * These are precolored (from 0 to N-1). *)
  let (color_map, _) = List.fold_left
    (fun (cm, ci) arg -> (VMap.add arg ci cm, ci + 1))
    (VMap.empty, 0)
    args
  in
  assign_colors ~color_count ~color_map ~spilled:VSet.empty ~removed


(* Rewrite a fragment of assembly, applying the mapping from variables to registers. *)
let rec subst_registers acc subst (asm : t list) : t list =
  let subst_var x =
    try
      VMap.find x subst
    with Not_found ->
      printf "x: %d\n" x;
      assert false
  in
  let subst_operand op =
    match op with
    | Reg x   -> Reg (VMap.find x subst)
    | Const _ -> op
  in
  match asm with
  | ADD (op1, op2, z) :: tail ->
      subst_registers (ADD (subst_operand op1, subst_operand op2, subst_var z) :: acc) subst tail
  | SUB (op1, op2, z) :: tail ->
      subst_registers (SUB (subst_operand op1, subst_operand op2, subst_var z) :: acc) subst tail
  | MUL (op1, op2, z) :: tail ->
      subst_registers (MUL (subst_operand op1, subst_operand op2, subst_var z) :: acc) subst tail
  | DIV (op1, op2, z) :: tail ->
      subst_registers (DIV (subst_operand op1, subst_operand op2, subst_var z) :: acc) subst tail
  | MOD (op1, op2, z) :: tail ->
      subst_registers (MOD (subst_operand op1, subst_operand op2, subst_var z) :: acc) subst tail
  | JE (op1, op2, label) :: tail ->
      subst_registers (JE (subst_operand op1, subst_operand op2, label) :: acc) subst tail
  | JL (op1, op2, label) :: tail ->
      subst_registers (JL (subst_operand op1, subst_operand op2, label) :: acc) subst tail
  | LOAD (v1, v2) :: tail ->
      subst_registers (LOAD (subst_var v1, subst_var v2) :: acc) subst tail
  | STORE (v1, op2) :: tail ->
      subst_registers (STORE (subst_var v1, subst_operand op2) :: acc) subst tail
  | CALL_VS2 (f_id, args, z) :: tail ->
      subst_registers (CALL_VS2 (f_id, List.map subst_operand args, subst_var z) :: acc) subst tail
  | RET op :: tail ->
      subst_registers (RET (subst_operand op) :: acc) subst tail
  | (JUMP label as inst) :: tail | (Label label as inst) :: tail ->
      subst_registers (inst :: acc) subst tail
  | [] ->
      List.rev acc


type spill_t = {
  reg_offsets : int IMap.t;   (* Offsets into spill array where the virtual registers are stored *)
  root_ref    : int           (* Register used for holding the root reference to the spill array *)
}


let inject_loads ~spilled_reg_offsets ~reg_count ~reg ~root_ref =
  if IMap.mem reg spilled_reg_offsets then
    let load_asm = [
      CALL_VS2 (AsmName "zml_deref_root", [Reg root_ref], reg_count);
      CALL_VS2 (AsmName "zml_array_get",
        [Reg reg_count; Const (IMap.find reg spilled_reg_offsets)], reg_count)
    ] in
    (reg_count + 1, Reg reg_count, load_asm)
  else
    (reg_count, Reg reg, [])


let inject_stores ~spilled_reg_offsets ~reg_count ~reg ~root_ref =
  if IMap.mem reg spilled_reg_offsets then
    (* Leave a register available for the destructive write which
     * precedes this injected assembly *)
    let written_reg = reg_count in
    let reg_count   = reg_count + 1 in
    let store_asm = [
      CALL_VS2 (AsmName "zml_deref_root", [Reg root_ref], reg_count);
      CALL_VS2 (AsmName "zml_array_set",
        [Reg reg_count; Const (IMap.find reg spilled_reg_offsets); Reg written_reg], written_reg)
    ] in
    (reg_count + 1, written_reg, store_asm)
  else
    (reg_count, reg, [])


(* Rewrite an arbitrary virtual zasm instruction, inserting loads and stores as necessary to ensure
 * that spilled registers are accessed via the spill array. *)
let spill_instruction 
  ~(asm_acc : t list)                 (* Accumulator for assembly: output is prepended to this *)
  ~(spilled_reg_offsets : int IMap.t) (* Locations of spilled regs in spill array *)
  ~(reg_count : int)                  (* Count of virtual assembly registers used by this asm *)
  ~(root_ref : int)                   (* Virtual reg which holds the spill array root reference *)
  ~(make_inst : operand_t list -> reg_t option -> t)
                                      (* Constructor for the instruction currently being analyzed *)
  ~(ops : operand_t list)             (* Instruction operands (instruction treats them as read-only) *)
  ~(res_opt : reg_t option)           (* Result register, if appropriate *)
    : int                             (* Updated count of virtual assembly registers *)
    * t list =                        (* Resulting assembly, reverse-prepended to [asm_acc] *)
  let (reg_count, ops, injected_load_asm) = List.fold_left
    (fun (reg_count, ops_acc, injected_asm_acc) op ->
      match op with
      | Reg reg ->
          let (reg_count, op, injected) =
            inject_loads ~spilled_reg_offsets ~reg_count ~reg ~root_ref
          in
          (reg_count, ops_acc @ [op], injected_asm_acc @ injected)
      | Const _ ->
          (reg_count, ops_acc @ [op], injected_asm_acc))
    (reg_count, [], [])
    ops
  in
  let (reg_count, res_opt, injected_store_asm) =
    match res_opt with
    | None ->
        (reg_count, res_opt, [])
    | Some res ->
        let (reg_count, res, inject) =
          inject_stores ~spilled_reg_offsets ~reg_count ~reg:res ~root_ref
        in
        (reg_count, Some res, inject)
  in
  let replacement_inst = make_inst ops res_opt in
  let replacement_asm  = injected_load_asm @ [replacement_inst] @ injected_store_asm in
  (reg_count, List.rev_append replacement_asm asm_acc)


(* Convenience function which invokes [spill_instruction] for the common case of
 * binary operations (e.g. ADD, SUB, etc.). *)
let spill_bin_op ~asm_acc ~spilled_reg_offsets ~reg_count ~root_ref
    ~(make_inst : operand_t -> operand_t -> reg_t -> t) ~op1 ~op2 ~res =
  let si_make_inst op_list res_opt =
    match (op_list, res_opt) with
    | ([op1; op2], Some res) ->
        make_inst op1 op2 res
    | _ ->
        assert false
  in
  spill_instruction ~asm_acc ~spilled_reg_offsets ~reg_count ~root_ref
    ~make_inst:si_make_inst ~ops:[op1; op2] ~res_opt:(Some res)


(* Modify the given virtual assembly so that it allocates an array off the
 * heap to use for storage for the [spill_regs]. *)
let spill_to_heap
  (spill_regs : VSet.t) (* Virtual registers to be moved to heap storage *)
  (root_ref : reg_t)    (* Virtual register to use for the spill array reference *)
  (reg_count : int)     (* Count of virtual registers used by this assembly (0 to N-1) *)
  (asm : t list)        (* Assembly to be modified *)
    : t list =          (* Modified assembly *)
  (* Assign spilled registers to slots in the spill array, in sorted order *)
  let (_, spilled_reg_offsets) = VSet.fold
    (fun x (i, m) -> (i + 1, IMap.add x i m))
    spill_regs
    (0, IMap.empty)
  in
  let header =  [
    CALL_VS2 (AsmName "zml_alloc_value_array", [Const (VSet.cardinal spill_regs); Const 0], root_ref);
    CALL_VS2 (AsmName "zml_register_root", [Reg root_ref], root_ref)
  ] in
  (* Insert loads and stores whenever the spilled registers are accessed. *)
  let (reg_count, modified_asm) = List.fold_left
    (fun (reg_count, asm_acc) inst ->
      match inst with
      | ADD (op1, op2, r) ->
          spill_bin_op ~asm_acc ~spilled_reg_offsets ~reg_count ~root_ref
            ~make_inst:(fun x y z -> ADD (x, y, z)) ~op1 ~op2 ~res:r
      | SUB (op1, op2, r) ->
          spill_bin_op ~asm_acc ~spilled_reg_offsets ~reg_count ~root_ref
            ~make_inst:(fun x y z -> SUB (x, y, z)) ~op1 ~op2 ~res:r
      | MUL (op1, op2, r) ->
          spill_bin_op ~asm_acc ~spilled_reg_offsets ~reg_count ~root_ref
            ~make_inst:(fun x y z -> MUL (x, y, z)) ~op1 ~op2 ~res:r
      | DIV (op1, op2, r) ->
          spill_bin_op ~asm_acc ~spilled_reg_offsets ~reg_count ~root_ref
            ~make_inst:(fun x y z -> DIV (x, y, z)) ~op1 ~op2 ~res:r
      | MOD (op1, op2, r) ->
          spill_bin_op ~asm_acc ~spilled_reg_offsets ~reg_count ~root_ref
            ~make_inst:(fun x y z -> MOD (x, y, z)) ~op1 ~op2 ~res:r
      | JE (op1, op2, label) ->
          let make_inst op_list res_opt =
            match (op_list, res_opt) with
            | ([o1; o2], None) ->
                JE (o1, o2, label)
            | _ ->
                assert false
          in
          spill_instruction ~asm_acc ~spilled_reg_offsets ~reg_count ~root_ref
            ~make_inst ~ops:[op1; op2] ~res_opt:None
      | JL (op1, op2, label) ->
          let make_inst op_list res_opt =
            match (op_list, res_opt) with
            | ([o1; o2], None) ->
                JL (o1, o2, label)
            | _ ->
                assert false
          in
          spill_instruction ~asm_acc ~spilled_reg_offsets ~reg_count ~root_ref
            ~make_inst ~ops:[op1; op2] ~res_opt:None
      | LOAD (reg1, reg2) ->
          let make_inst op_list res_opt =
            match (op_list, res_opt) with
            | ([Reg r1], Some r2) ->
                LOAD (r1, r2)
            | _ ->
                assert false
          in
          spill_instruction ~asm_acc ~spilled_reg_offsets ~reg_count ~root_ref
            ~make_inst ~ops:[Reg reg1] ~res_opt:(Some reg2)
      | CALL_VS2 (routine, op_list, result_reg) ->
          let make_inst ops res_opt =
            match res_opt with
            | Some res ->
                CALL_VS2 (routine, ops, res)
            | None ->
                assert false
          in
          spill_instruction ~asm_acc ~spilled_reg_offsets ~reg_count ~root_ref
            ~make_inst ~ops:op_list ~res_opt:(Some result_reg)
      | STORE (reg1, op2) ->
          let make_inst op_list res_opt =
            match (op_list, res_opt) with
            | ([o2], Some r1) ->
                STORE (r1, o2)
            | _ ->
                assert false
          in
          spill_instruction ~asm_acc ~spilled_reg_offsets ~reg_count ~root_ref
            ~make_inst ~ops:[op2] ~res_opt:(Some reg1)
      | RET op ->
          begin match op with
          | Const _ ->
              (reg_count,
                RET op ::
                CALL_VS2 (AsmName "zml_unregister_root", [Reg root_ref], root_ref) ::
                asm_acc)
          | Reg r ->
              let (reg_count, op, load_asm) =
                inject_loads ~spilled_reg_offsets:spilled_reg_offsets ~reg_count ~reg:r ~root_ref
              in
              (reg_count,
                RET op ::
                CALL_VS2 (AsmName "zml_unregister_root", [Reg root_ref], root_ref) ::
                (List.rev_append load_asm asm_acc))
          end
      | (JUMP label as inst) | (Label label as inst) ->
          (reg_count, inst :: asm_acc))
    (reg_count, [])
    asm
  in
  header @ (List.rev modified_asm)


(* Allocate registers for the block of assembly.  The assembly is modified
 * to reflect the register allocation; if necessary, the assembly is also
 * modified to spill registers to a heap-allocated value array. *)
let rec alloc_registers
  ?(spilled_regs=VSet.empty)      (* Virtual registers which have been spilled previously *)
  (precolored_regs : reg_t list)  (* Virtual registers which must be assigned to specific zasm regs *)
  (asm : t list)                  (* Virtual asm to be analyzed *)
  (reg_count : int)               (* Count of virtual regs used by the asm *)
    : t list =
  let (modified_asm, precolored_regs) =
    if VSet.is_empty spilled_regs then
      (asm, precolored_regs)
    else
      (* The spill_to_heap implementation uses an additional register to store a reference
       * to the spill array, and this reference is maintained across the entire function body.
       * It doesn't make sense to ever consider spilling this register, so we'll precolor it. *)
      let root_ref  = reg_count in
      let reg_count = reg_count + 1 in
      (spill_to_heap spilled_regs root_ref reg_count asm, precolored_regs @ [root_ref])
  in
  let g = make_interference_graph modified_asm in
  match color_graph precolored_regs local_variable_count g with
  | Colored color_map ->
      begin try
        subst_registers [] color_map modified_asm
      with Not_found ->
        assert false
      end
  | Spilled new_spilled_regs ->
      (* Note: intentionally passing the original assembly here, not the assembly modified with heap
       * spilling operations.  Only the set of spilled registers changes as we recurse.  (The
       * introduction of heap management operations adds additional register pressure which may lead
       * to further register spilling.  If that happens, we don't want to allocate a *second* spill
       * array... we just want to restart the heap spilling with a *larger* spill array.) *)
      let spilled_regs = VSet.union spilled_regs new_spilled_regs in
      alloc_registers ~spilled_regs precolored_regs asm reg_count


(* Compile a function, yielding an assembly listing for the function body. *)
let compile (f_args : var_t list) (f_body : Function.expr_t) : t list =
  let virtual_args, virtual_asm, virtual_reg_count = compile_virtual f_args f_body in
  alloc_registers virtual_args virtual_asm virtual_reg_count


