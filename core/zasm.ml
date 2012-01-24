
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
let local_variable_count = 15


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
  | CALL_VS2 of var_t * (operand_t list) * reg_t
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
      (state, [CALL_VS2 (g, arg_regs, result_reg)])

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
let compile_virtual (f_args : var_t list) (f_body : Function.expr_t) : (reg_t list) * (t list) =
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
  (List.map (fun x -> VMap.find x state.reg_of_var) f_args, assembly @ [RET (Reg result_reg)])



(* Node of a control flow graph. *)
type cfg_node_t = {
  instruction : t;            (* Instruction under consideration *)
  successors  : int list;     (* Offsets of instructions which may follow this one *)
  gen         : VSet.t;       (* Set of variables which are read by the instruction *)
  kill        : VSet.t;       (* Set of variables which are written by the instruction *)
  live_in     : VSet.t;       (* Set of variables which are live immediately before this instruction *)
  live_out    : VSet.t        (* Set of variables which are live immediately after this instruction *)
}


(* Generate a lookup table for the offsets at which labels are found in
 * an assembly fragment. *)
let make_label_table asm =
  let label_offsets = Hashtbl.create 10 in
  let _ = List.fold_left
    (fun i inst ->
      match inst with
      | Label label ->
          let () = assert (not (Hashtbl.mem label_offsets label)) in
          let () = Hashtbl.add label_offsets label i in
          (i + 1)
      | _ ->
          (i + 1))
    0
    asm
  in
  label_offsets


(* Initialize the control flow graph, in preparation for iterative solution. *)
let init_control_flow_graph (asm : t list) : cfg_node_t array =
  let cfg_len = List.length asm in
  let cfg = Array.make cfg_len {
    instruction = Label 0;
    successors  = [];
    gen         = VSet.empty;
    kill        = VSet.empty;
    live_in     = VSet.empty;
    live_out    = VSet.empty
  } in
  let label_offsets = make_label_table asm in
  let item_count = List.fold_left
    (fun i inst ->
      let arr_item =
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
              successors  = (Hashtbl.find label_offsets label) :: default_node.successors
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
            successors = [Hashtbl.find label_offsets label];
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
      in
      let () = cfg.(i) <- arr_item in
      (i + 1))
    0
    asm
  in
  let () = assert ((item_count : int) = cfg_len) in
  cfg


(* Solve for the sets of variables which are "live" before and after every instruction. *)
let solve_liveness (asm : t list) : cfg_node_t array =
  let rec fixpoint graph =
    let next_graph = Array.copy graph in
    for i = 0 to (Array.length graph) - 1 do
      let old = graph.(i) in
      let outputs_not_killed = VSet.diff old.live_out old.kill in
      let successor_inputs = List.fold_left
        (fun acc j -> VSet.union acc graph.(j).live_in)
        VSet.empty
        old.successors
      in
      next_graph.(i) <- { old with
      live_in  = VSet.union old.gen outputs_not_killed;
        live_out = successor_inputs
      }
    done;
    if next_graph = graph then
      graph
    else
      fixpoint next_graph
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
  let all_variables = Array.fold_left
    (fun acc node -> VSet.union (VSet.union acc node.gen) node.kill)
    VSet.empty
    liveness
  in
  let graph_with_vertices = VSet.fold
    (fun x acc -> VMap.add x VSet.empty acc)
    all_variables
    VMap.empty
  in
  Array.fold_left
    (fun acc node -> vmap_naive_union acc (interfering_of_instruction node))
    graph_with_vertices
    liveness


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


(* Allocate registers for the block of assembly. *)
let alloc_registers (arg_regs : reg_t list) (asm : t list) : t list =
  let g = make_interference_graph asm in
  match color_graph arg_regs local_variable_count g with
  | Colored color_map ->
      begin try
        subst_registers [] color_map asm
      with Not_found ->
        assert false
      end
  | Spilled _ ->
      (* TODO *)
      assert false
      

(* Compile a function, yielding an assembly listing for the function body. *)
let compile (f_args : var_t list) (f_body : Function.expr_t) : t list =
  let virtual_args, virtual_asm = compile_virtual f_args f_body in
  alloc_registers virtual_args virtual_asm


