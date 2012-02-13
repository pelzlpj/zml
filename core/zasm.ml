(* Compilation of functions (i.e. [Function.function_t]) into Z-Machine assembly.
 *
 * No assumptions are made within this module regarding the specific format in which the Z-Machine
 * instructions should be emitted for assembly.  See module [Zapf] for code which targets the Zapf
 * assembler.
 *)

open Printf

module VarID = Normal.VarID
module VMap  = Normal.VMap
type var_t   = Normal.var_t


(********************************************************************************
 * REGISTER TYPES
 *
 * The compilation strategy proceeds in two phases:
 *
 *    1) Given a function to compile, of type [Function.function_t], generate
 *       "virtual" Z-Machine assembly which implements the function.  This is
 *       assembly which targets a Z-Machine with an infinite number of registers
 *       (aka "local variables") available.
 *
 *    2) Perform register allocation, mapping a potentially large number of
 *       virtual Z-Machine registers to the actual set available on the
 *       Z-Machine.
 *
 * To avoid some classes of programming errors, the virtual and physical
 * registers are encoded into the type system as abstract types VReg.t and
 * ZReg.t, respectively.  The type definitions follow.
 ********************************************************************************)

(* Opaque identifiers for registers in Z-Machine virtual assembly *)
module type ZASM_REG = sig
  type t

  val int_of : t -> int
  val of_int : int -> t
  val string_of : t -> string

  val compare : t -> t -> int
end

module VReg : ZASM_REG = struct
  (* The type of *virtual* Z-Machine registers (no limit on register count) *)
  type t = int

  let int_of x = x
  let of_int x = x
  let string_of x = sprintf "vr%d" x

  let compare e1 e2 = if e1 < e2 then -1 else if e1 > e2 then 1 else 0
end

module VRegSet = Set.Make(VReg)
module VRegMap = Map.Make(VReg)
let vregset_of_list = List.fold_left (fun acc x -> VRegSet.add x acc) VRegSet.empty

module VRegState = struct
  type t = int  (* The type of a state variable for allocating virtual registers *)

  (* Allocate the next available virtual register *)
  let next (state : t) : (t * VReg.t) = (state + 1, VReg.of_int state)

  (* Empty initial state for register allocation *)
  let empty : t = 0
end


module ZReg : ZASM_REG = struct
  (* The type of *physical* Z-Machine registers *)
  type t = int

  let int_of x = x
  let of_int x = x
  let string_of x = sprintf "r%d" x

  let compare e1 e2 = if e1 < e2 then -1 else if e1 > e2 then 1 else 0
end

module ZRegSet = Set.Make(ZReg)
let zregset_of_list = List.fold_left (fun acc x -> ZRegSet.add (ZReg.of_int x) acc) ZRegSet.empty

module ZRegState = struct
  (* The type of a state variable for allocating virtual registers *)
  type t = int

  (* Allocate the next available virtual register *)
  let next (state : t) : (t * ZReg.t) = (state + 1, ZReg.of_int state)

  (* Empty initial state for register allocation *)
  let empty : t = 0
end


(* Identifiers for labels placed within a function body *)
type label_t = int


(* Constant values passed into opcodes fall into these categories *)
type const_t =
  | ConstNum of int           (* Plain old integer used as an operand *)
  | MappedRoutine of var_t    (* Typical form for calling a routine by internal ZML id *)
  | AsmRoutine of string      (* Directly injecting the name of an assembly routine *)


(* Most opcodes accept either variable identifiers (v0-v255) or integer constants as operands.
 *
 * The type parameter allows us to differentiate between instructions operating on the virtual
 * register set, and instructions operating on the physical register set. *)
type 'a operand_t =
  | Reg of 'a
  | Const of const_t



(* We need only a small subset of Z-machine opcodes in order to implement
 * [Function.expr_t].  In the future, it may prove useful to use additional
 * opcodes to handle special cases.  It probably won't matter for performance,
 * but the code size could be reduced by using more compact instructions. *)
type 'a t =
  | ADD of 'a operand_t * 'a operand_t * 'a
  | SUB of 'a operand_t * 'a operand_t * 'a
  | MUL of 'a operand_t * 'a operand_t * 'a
  | DIV of 'a operand_t * 'a operand_t * 'a
  | MOD of 'a operand_t * 'a operand_t * 'a
  | JE  of 'a operand_t * 'a operand_t * label_t
  | JL  of 'a operand_t * 'a operand_t * label_t
  | JUMP of label_t
  | LOAD of 'a * 'a
  | STORE of 'a * 'a operand_t
  | CALL_VS2 of 'a operand_t * ('a operand_t list) * 'a
  | RET of 'a operand_t
  | Label of label_t



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
    | Function.NativeFunc _
    | Function.NativeClosure _ ->
        sprintf "%s_%s" short_name (VarID.to_int_string f_id)
    | Function.ExtFunc (ext_impl, _) ->
        ext_impl


type compile_state_t = {
  reg_of_var : VReg.t VMap.t; (* Maps Normal.t variables to virtual Z-Machine registers *)
  reg_state  : VRegState.t;   (* Tracks virtual registers used *)
  label_count: int            (* Number of labels emitted *)
}

let rec compile_virtual_aux
  (state : compile_state_t)   (* Compilation context *)
  (result_reg)                (* Register which should be used to store the result *)
  (expr : Function.expr_t)    (* Expression to be compiled *)
    : compile_state_t         (* New context *)
    * VReg.t t list =         (* List of instructions for the expression *)
  match expr with
  | Function.Unit ->
      (* For now we're treating unit as integer zero.  It shouldn't matter. *)
      compile_virtual_aux state result_reg (Function.Int 0)
  | Function.Int i ->
      (state, [STORE (result_reg, Const (ConstNum i))])
  | Function.BinaryOp (op, a, b) ->
      let ctor =
        match op with
        | Normal.Add -> (fun x y z -> ADD (x, y, z))
        | Normal.Sub -> (fun x y z -> SUB (x, y, z))
        | Normal.Mul -> (fun x y z -> MUL (x, y, z))
        | Normal.Div -> (fun x y z -> DIV (x, y, z))
        | Normal.Mod -> (fun x y z -> MOD (x, y, z))
      in
      compile_virtual_binary_int state result_reg ctor a b
  | Function.UnaryOp (Normal.Neg, a) ->
      (* Negation is implemented as subtraction from zero. *)
      (state, [SUB (Const (ConstNum 0), Reg (VMap.find a state.reg_of_var), result_reg)])
  | Function.Conditional (Normal.IfEq, a, b, e1, e2) ->
      compile_virtual_if state result_reg true a b e1 e2
  | Function.Conditional (Normal.IfLess, a, b, e1, e2) ->
      compile_virtual_if state result_reg false a b e1 e2
  | Function.Var a ->
      begin try
        (state, [LOAD (VMap.find a state.reg_of_var, result_reg)])
      with Not_found ->
        (* If there is no register associated with this variable, then
         * this must be a reference to a function name.
         *
         * FIXME: this sucks and feels brittle.  The type system should encode this info. *)
        (state, [STORE (result_reg, Const (MappedRoutine a))])
      end
  | Function.Let (a, e1, e2) ->
      (* "let" just leads to emitting instructions for [e1] prior to [e2],
       * with the additional constraint that [a] becomes an alias for the
       * [e1] result register while compiling [e2]. *)
      let (next_state, head_result_reg) = VRegState.next state.reg_state in
      let state = {state with reg_state = next_state} in
      let (state, head_asm) = compile_virtual_aux state head_result_reg e1 in
      let new_binding_state = {state with reg_of_var = VMap.add a head_result_reg state.reg_of_var} in
      let (state, tail_asm) = compile_virtual_aux new_binding_state result_reg e2 in
      (state, head_asm @ tail_asm)
  | Function.ApplyKnown (g, g_args) ->
      let arg_regs = List.map (fun v -> Reg (VMap.find v state.reg_of_var)) g_args in
      (state, [CALL_VS2 (Const (MappedRoutine g), arg_regs, result_reg)])
  | Function.ApplyUnknown (g, g_args) ->
      let g_reg    = VMap.find g state.reg_of_var in
      let arg_regs = List.map (fun v -> Reg (VMap.find v state.reg_of_var)) g_args in
      (state, [CALL_VS2 (Reg g_reg, arg_regs, result_reg)])
  | Function.RefArrayAlloc (size, init) ->
      (* TODO *)
      assert false
  | Function.ValArrayAlloc (size, init) ->
      (* TODO *)
      assert false
  | Function.RefArraySet (arr, index, v) ->
      (* TODO *)
      assert false
  | Function.ValArraySet (arr, index, v) ->
      (* TODO *)
      assert false
  | Function.RefArrayGet (arr, index) ->
      (* TODO *)
      assert false
  | Function.ValArrayGet (arr, index) ->
      (* TODO *)
      assert false


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
    : (VReg.t list)             (* Virtual registers assigned to function arguments *)
    * (VReg.t t list)           (* Generated virtual assembly *)
    * VRegState.t =             (* State of virtual register allocation *)
  (* FIXME *)
  (* call_vs2 supports 0 through 7 arguments.  Implementing functions with
   * more than seven arguments will require heap-allocating a reference array
   * as storage for the extra args.  Possibly this can be handled using the same
   * code path as closures. *)
  let () = assert (List.length f_args <= call_vs2_max_args) in
  (* Assign virtual registers for the function arguments and the return value *)
  let (reg_state, result_reg) = VRegState.next VRegState.empty in
  let init_state = List.fold_left
    (fun acc arg ->
      let (next_state, new_reg) = VRegState.next acc.reg_state in
      {acc with
        reg_of_var = VMap.add arg new_reg acc.reg_of_var;
        reg_state  = next_state})
    {reg_of_var = VMap.empty; reg_state; label_count = 0}
    f_args
  in
  let (state, assembly) = compile_virtual_aux init_state result_reg f_body in
  (List.map (fun x -> VMap.find x state.reg_of_var) f_args,
    assembly @ [RET (Reg result_reg)],
    state.reg_state)



(* Node of a control flow graph. *)
type cfg_node_t = {
  instruction : VReg.t t;     (* Instruction under consideration *)
  successors  : int list;     (* Offsets of instructions which may follow this one *)
  gen         : VRegSet.t;    (* Set of variables which are read by the instruction *)
  kill        : VRegSet.t;    (* Set of variables which are written by the instruction *)
  live_in     : VRegSet.t;    (* Set of variables which are live immediately before this instruction *)
  live_out    : VRegSet.t     (* Set of variables which are live immediately after this instruction *)
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
    (inst : VReg.t t)             (* Instruction for this node *)
      : cfg_node_t =
  let default_node = {
    instruction = inst;
    successors  = if i < cfg_len then [i + 1] else [];
    gen         = VRegSet.empty;
    kill        = VRegSet.empty;
    live_in     = VRegSet.empty;
    live_out    = VRegSet.empty
  } in
  match inst with
  | ADD (op1, op2, v3) | SUB (op1, op2, v3) | MUL (op1, op2, v3)
  | DIV (op1, op2, v3) | MOD (op1, op2, v3) ->
      let binary_op_node = { default_node with kill = VRegSet.singleton v3 } in
      begin match (op1, op2) with
      | (Reg v1, Reg v2) ->
          { binary_op_node with gen = vregset_of_list [v1; v2] }
      | (Reg v1, Const _) | (Const _, Reg v1) ->
          { binary_op_node with gen = VRegSet.singleton v1 }
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
          { branch_node with gen = vregset_of_list [v1; v2] }
      | (Reg v1, Const _) | (Const _, Reg v1) ->
          { branch_node with gen = VRegSet.singleton v1 }
      | (Const _, Const _) ->
          branch_node
      end
  | JUMP label -> { default_node with
      successors = [LMap.find label label_offsets];
    }
  | LOAD (v1, v2) -> { default_node with
      gen  = VRegSet.singleton v1;
      kill = VRegSet.singleton v2
    }
  | STORE (v1, op2) ->
      let store_node = { default_node with kill = VRegSet.singleton v1 } in
      begin match op2 with
      | Reg v2 -> { store_node with gen = VRegSet.singleton v2 }
      | Const _ -> store_node
      end
  | CALL_VS2 (f_id, args, result) ->
      List.fold_left
        (fun acc arg ->
          match arg with
          | Reg v   -> { acc with gen = VRegSet.add v acc.gen }
          | Const _ -> acc)
        { default_node with kill = VRegSet.singleton result }
        args
  | RET op ->
      let return_node = { default_node with successors = [] } in
      begin match op with
      | Reg v   -> { return_node with gen = VRegSet.singleton v }
      | Const _ -> return_node
      end
  | Label _ ->
      default_node


(* Initialize the control flow graph, in preparation for iterative solution. *)
let init_control_flow_graph (asm : VReg.t t list) : cfg_node_t IMap.t =
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
let solve_liveness (asm : VReg.t t list) : cfg_node_t IMap.t =
  let rec fixpoint graph =
    let next_graph = IMap.fold
      (fun i old_node acc ->
        let outputs_not_killed = VRegSet.diff old_node.live_out old_node.kill in
        let successor_inputs = List.fold_left
          (fun acc j -> VRegSet.union acc (IMap.find j graph).live_in)
          VRegSet.empty
          old_node.successors
        in
        let new_node = { old_node with
          live_in  = VRegSet.union old_node.gen outputs_not_killed;
          live_out = successor_inputs
        } in
        IMap.add i new_node acc)
      graph
      IMap.empty
    in
    if next_graph = graph then graph else fixpoint next_graph
  in
  fixpoint (init_control_flow_graph asm)


(* As VRegSet.fold, but iterating over elements of the product of the two sets. *)
let vregset_fold_product f s1 s2 init =
  VRegSet.fold
    (fun s1_x s1_acc ->
      VRegSet.fold
        (fun s2_x s2_acc -> f s1_x s2_x s2_acc)
        s2
        s1_acc)
    s1
    init


let vregset_map f (s : VRegSet.t) : ZRegSet.t =
  VRegSet.fold
    (fun x acc -> ZRegSet.add (f x) acc) 
    s
    ZRegSet.empty


let vregmap_naive_union m1 m2 =
  VRegMap.merge
    (fun key m1_val_opt m2_val_opt ->
      match (m1_val_opt, m2_val_opt) with
      | (Some m1_val, Some m2_val) ->
          Some (VRegSet.union m1_val m2_val)
      | (Some v, None) | (None, Some v) ->
          Some v
      | (None, None) ->
          None)
    m1
    m2


exception Found_first of VReg.t

(* Finds the first element in the collection which satisfies the
 * predicate, if any. *)
let vregmap_find_first (p : VReg.t -> 'a -> bool) (m : 'a VRegMap.t) : VReg.t option =
  try
    let () = VRegMap.iter
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
  

(* Generate an interference graph for the virtual zasm assembly.  The resulting data structure maps
 * each virtual register to a set of virtual registers with which it interferes. *)
let make_interference_graph (asm : VReg.t t list) : VRegSet.t VRegMap.t =
  let liveness = solve_liveness asm in
  (* Variable [x] interferes with [y] if [x] <> [y] and there is an
   * instruction such that x \in kill and y \in live_out. *)
  let interfering_of_instruction inst_node =
    vregset_fold_product
      (fun kill_item out_item acc ->
        if kill_item = out_item then
          acc
        else
          (* Creating mappings in both directions... *)
          let kill_mapping =
            let old_kill_binding = try VRegMap.find kill_item acc with Not_found -> VRegSet.empty in
            VRegMap.add kill_item (VRegSet.add out_item old_kill_binding) acc
          in
          let old_out_binding = try VRegMap.find out_item kill_mapping with Not_found -> VRegSet.empty in
          VRegMap.add out_item (VRegSet.add kill_item old_out_binding) kill_mapping)
      inst_node.kill
      inst_node.live_out
      VRegMap.empty
  in
  (* All variables should be present in the graph, regardless of whether they interfere with
   * other variables.  So start with a graph containing only vertices (no edges). *)
  let all_variables = IMap.fold
    (fun _ node acc -> VRegSet.union (VRegSet.union acc node.gen) node.kill)
    liveness
    VRegSet.empty
  in
  let graph_with_vertices = VRegSet.fold
    (fun x acc -> VRegMap.add x VRegSet.empty acc)
    all_variables
    VRegMap.empty
  in
  IMap.fold
    (fun _ node acc -> vregmap_naive_union acc (interfering_of_instruction node))
    liveness
    graph_with_vertices


let print_interference_graph graph =
  VRegMap.iter
    (fun var connected ->
      let connected_s = String.concat ", "
        (List.rev (VRegSet.fold (fun x acc -> (VReg.string_of x) :: acc) connected []))
      in
      printf "%s: %s\n" (VReg.string_of var) connected_s)
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
  | Colored of ZReg.t VRegMap.t (* Successful coloring, with the map from virt registers to phys registers *)
  | Spilled of VRegSet.t        (* Coloring failed; one or more virtual registers were spilled *)


(* Select colors for the nodes removed by [simplify_color_graph]. *)
let rec assign_colors
  ~(color_count : int)                    (* Count of colors/registers available *)
  ~(color_map : ZReg.t VRegMap.t)         (* Accumulator for the resulting register allocation *)
  ~(spilled : VRegSet.t)                  (* Accumulator for spilled nodes *)
  ~(removed : (VReg.t * VRegSet.t) list)  (* Stack of nodes to be processed *)
    : coloring_t =
  let all_colors = zregset_of_list (list_range color_count) in
  match removed with
  | [] ->
      if VRegSet.cardinal spilled > 0 then
        Spilled spilled
      else
        Colored color_map
  | (x, connected_nodes) :: tail ->
      let connected_unspilled_nodes = VRegSet.diff connected_nodes spilled in
      (* Due to use of [removed] as a stack, the [connected_nodes] will
       * always have been colored on a previous iteration.  So the [find]
       * never fails. *)
      let connected_colors = vregset_map (fun x -> VRegMap.find x color_map) connected_unspilled_nodes in
      let avail_colors = ZRegSet.diff all_colors connected_colors in
      if ZRegSet.cardinal avail_colors > 0 then
        let color_map = VRegMap.add x (ZRegSet.choose avail_colors) color_map in
        assign_colors ~color_count ~color_map ~spilled ~removed:tail
      else
        (* Coloring failure.  Spill this node and continue. *)
        assign_colors ~color_count ~color_map ~spilled:(VRegSet.add x spilled) ~removed:tail


(* Remove a node, and all connected edges, from the graph. *)
let remove_graph_node x g =
  let connected_nodes = VRegMap.find x g in
  let purged_graph =
    VRegSet.fold
      (fun connected_node acc ->
        let connected_node_connections = VRegMap.find connected_node acc in
        VRegMap.add connected_node (VRegSet.remove x connected_node_connections) acc)
      connected_nodes
      (VRegMap.remove x g)
  in
  (connected_nodes, purged_graph)


(* Simplify a color graph by removing nodes.  First we remove nodes with fewer
 * than [color_count] colors, then we optimistically remove the other nodes.
 * As an exception, the function args are *not* removed from the graph.
 * We "precolor" them in place to reflect the Z-machine argument passing convention. *)
let rec simplify_color_graph (args : VReg.t list) color_count removed g =
  match vregmap_find_first
    (fun x connected -> (not (List.mem x args)) && VRegSet.cardinal connected < color_count)
    g
  with
  | Some x ->
      (* Found a non-argument node with fewer than [color_count] connections. *)
      let (connected_nodes, purged_graph) = remove_graph_node x g in
      simplify_color_graph args color_count ((x, connected_nodes) :: removed) purged_graph
  | None ->
      (* Failed to find a non-argument node with fewer than [color_count] connections.  Relax the
       * restriction; check for non-argument nodes without regard for number of connections. *)
      begin match vregmap_find_first
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
let color_graph (args : VReg.t list) color_count graph =
  let removed = simplify_color_graph args color_count [] graph in
  (* The only nodes remaining in the simplified graph are the argument-passing nodes.
   * These are precolored (from 0 to N-1). *)
  let (color_map, _) = List.fold_left
    (fun (cm, cr_state) arg ->
      let (cr_state, cr) = ZRegState.next cr_state in
      (VRegMap.add arg cr cm, cr_state))
    (VRegMap.empty, ZRegState.empty)
    args
  in
  assign_colors ~color_count ~color_map ~spilled:VRegSet.empty ~removed


(* Rewrite a fragment of assembly, applying the mapping from virtual registers to physical registers. *)
let rec subst_registers (acc : ZReg.t t list) (subst : ZReg.t VRegMap.t) (asm : VReg.t t list) : ZReg.t t list =
  let subst_reg (x : VReg.t) : ZReg.t =
    try
      VRegMap.find x subst
    with Not_found ->
      assert false
  in
  let subst_operand (op : VReg.t operand_t) : ZReg.t operand_t =
    match op with
    | Reg x   -> Reg (VRegMap.find x subst)
    | Const x -> Const x
  in
  match asm with
  | ADD (op1, op2, z) :: tail ->
      subst_registers (ADD (subst_operand op1, subst_operand op2, subst_reg z) :: acc) subst tail
  | SUB (op1, op2, z) :: tail ->
      subst_registers (SUB (subst_operand op1, subst_operand op2, subst_reg z) :: acc) subst tail
  | MUL (op1, op2, z) :: tail ->
      subst_registers (MUL (subst_operand op1, subst_operand op2, subst_reg z) :: acc) subst tail
  | DIV (op1, op2, z) :: tail ->
      subst_registers (DIV (subst_operand op1, subst_operand op2, subst_reg z) :: acc) subst tail
  | MOD (op1, op2, z) :: tail ->
      subst_registers (MOD (subst_operand op1, subst_operand op2, subst_reg z) :: acc) subst tail
  | JE (op1, op2, label) :: tail ->
      subst_registers (JE (subst_operand op1, subst_operand op2, label) :: acc) subst tail
  | JL (op1, op2, label) :: tail ->
      subst_registers (JL (subst_operand op1, subst_operand op2, label) :: acc) subst tail
  | LOAD (v1, v2) :: tail ->
      subst_registers (LOAD (subst_reg v1, subst_reg v2) :: acc) subst tail
  | STORE (v1, op2) :: tail ->
      subst_registers (STORE (subst_reg v1, subst_operand op2) :: acc) subst tail
  | CALL_VS2 (f_id, args, z) :: tail ->
      let routine =
        match f_id with
        | Const (ConstNum i)      -> Const (ConstNum i)
        | Const (MappedRoutine m) -> Const (MappedRoutine m)
        | Const (AsmRoutine a)    -> Const (AsmRoutine a)
        | Reg r                   -> Reg (subst_reg r)
      in
      subst_registers (CALL_VS2 (routine, List.map subst_operand args, subst_reg z) :: acc) subst tail
  | RET op :: tail ->
      subst_registers (RET (subst_operand op) :: acc) subst tail
  | (JUMP label as inst) :: tail | (Label label as inst) :: tail ->
      subst_registers (inst :: acc) subst tail
  | [] ->
      List.rev acc



let inject_loads ~spilled_reg_offsets ~reg_alloc_state ~reg ~root_ref =
  if VRegMap.mem reg spilled_reg_offsets then
    let (reg_alloc_state, new_reg) = VRegState.next reg_alloc_state in
    let load_asm = [
      CALL_VS2 (Const (AsmRoutine "zml_deref_root"), [Reg root_ref], new_reg);
      CALL_VS2 (Const (AsmRoutine "zml_array_get"),
        [Reg new_reg; Const (ConstNum (VRegMap.find reg spilled_reg_offsets))], new_reg)
    ] in
    (reg_alloc_state, Reg new_reg, load_asm)
  else
    (reg_alloc_state, Reg reg, [])


let inject_stores ~spilled_reg_offsets ~reg_alloc_state ~reg ~root_ref =
  if VRegMap.mem reg spilled_reg_offsets then
    (* Leave a register available for the destructive write which
     * precedes this injected assembly *)
    let (reg_alloc_state, written_reg) = VRegState.next reg_alloc_state in
    let (reg_alloc_state, deref_reg)   = VRegState.next reg_alloc_state in
    let store_asm = [
      CALL_VS2 (Const (AsmRoutine "zml_deref_root"), [Reg root_ref], deref_reg);
      CALL_VS2 (Const (AsmRoutine "zml_array_set"),
        [Reg deref_reg; Const (ConstNum (VRegMap.find reg spilled_reg_offsets));
          Reg written_reg], written_reg)
    ] in
    (reg_alloc_state, written_reg, store_asm)
  else
    (reg_alloc_state, reg, [])


(* Rewrite an arbitrary virtual zasm instruction, inserting loads and stores as necessary to ensure
 * that spilled registers are accessed via the spill array. *)
let spill_instruction 
  ~(asm_acc : VReg.t t list)              (* Accumulator for assembly: output is prepended to this *)
  ~(spilled_reg_offsets : int VRegMap.t)  (* Locations of spilled virtual regs in spill array *)
  ~(reg_alloc_state : VRegState.t)        (* Describes the set of vregs already used by this assembly *)
  ~(root_ref : VReg.t)                    (* Virtual reg which holds the spill array root reference *)
  ~(make_inst : VReg.t operand_t list -> VReg.t option -> VReg.t t)
                                          (* Constructor for the instruction currently being analyzed *)
  ~(ops : VReg.t operand_t list)          (* Instruction operands (instruction treats them as read-only) *)
  ~(res_opt : VReg.t option)              (* Result register, if appropriate *)
    : int                                 (* Updated count of virtual assembly registers *)
    * VReg.t t list =                     (* Resulting assembly, reverse-prepended to [asm_acc] *)
  let (reg_alloc_state, ops, injected_load_asm) = List.fold_left
    (fun (reg_alloc_state, ops_acc, injected_asm_acc) op ->
      match op with
      | Reg reg ->
          let (reg_alloc_state, op, injected) =
            inject_loads ~spilled_reg_offsets ~reg_alloc_state ~reg ~root_ref
          in
          (reg_alloc_state, ops_acc @ [op], injected_asm_acc @ injected)
      | Const _ ->
          (reg_alloc_state, ops_acc @ [op], injected_asm_acc))
    (reg_alloc_state, [], [])
    ops
  in
  let (reg_alloc_state, res_opt, injected_store_asm) =
    match res_opt with
    | None ->
        (reg_alloc_state, res_opt, [])
    | Some res ->
        let (reg_alloc_state, res, inject) =
          inject_stores ~spilled_reg_offsets ~reg_alloc_state ~reg:res ~root_ref
        in
        (reg_alloc_state, Some res, inject)
  in
  let replacement_inst = make_inst ops res_opt in
  let replacement_asm  = injected_load_asm @ [replacement_inst] @ injected_store_asm in
  (reg_alloc_state, List.rev_append replacement_asm asm_acc)


(* Convenience function which invokes [spill_instruction] for the common case of
 * binary operations (e.g. ADD, SUB, etc.). *)
let spill_bin_op ~asm_acc ~spilled_reg_offsets ~reg_alloc_state ~root_ref
    ~(make_inst : VReg.t operand_t -> VReg.t operand_t -> VReg.t -> VReg.t t) ~op1 ~op2 ~res =
  let si_make_inst op_list res_opt =
    match (op_list, res_opt) with
    | ([op1; op2], Some res) ->
        make_inst op1 op2 res
    | _ ->
        assert false
  in
  spill_instruction ~asm_acc ~spilled_reg_offsets ~reg_alloc_state ~root_ref
    ~make_inst:si_make_inst ~ops:[op1; op2] ~res_opt:(Some res)


(* Modify the given virtual assembly so that it allocates an array off the
 * heap to use for storage for the [spill_regs]. *)
let spill_to_heap
  (spill_regs : VRegSet.t)        (* Virtual registers to be moved to heap storage *)
  (root_ref : VReg.t)             (* Virtual register to use for the spill array reference *)
  (reg_alloc_state : VRegState.t) (* Describes the set of vregs already used by this assembly *)
  (asm : VReg.t t list)           (* Assembly to be modified *)
    : VReg.t t list =             (* Modified assembly *)
  (* Assign spilled registers to slots in the spill array, in sorted order *)
  let (_, spilled_reg_offsets) = VRegSet.fold
    (fun x (i, m) -> (i + 1, VRegMap.add x i m))
    spill_regs
    (0, VRegMap.empty)
  in
  let header =  [
    CALL_VS2 (Const (AsmRoutine "zml_alloc_value_array"),
      [Const (ConstNum (VRegSet.cardinal spill_regs)); Const (ConstNum 0)], root_ref);
    CALL_VS2 (Const (AsmRoutine "zml_register_root"),
      [Reg root_ref], root_ref)
  ] in
  (* Insert loads and stores whenever the spilled registers are accessed. *)
  let (reg_alloc_state, modified_asm) = List.fold_left
    (fun (reg_alloc_state, asm_acc) inst ->
      match inst with
      | ADD (op1, op2, r) ->
          spill_bin_op ~asm_acc ~spilled_reg_offsets ~reg_alloc_state ~root_ref
            ~make_inst:(fun x y z -> ADD (x, y, z)) ~op1 ~op2 ~res:r
      | SUB (op1, op2, r) ->
          spill_bin_op ~asm_acc ~spilled_reg_offsets ~reg_alloc_state ~root_ref
            ~make_inst:(fun x y z -> SUB (x, y, z)) ~op1 ~op2 ~res:r
      | MUL (op1, op2, r) ->
          spill_bin_op ~asm_acc ~spilled_reg_offsets ~reg_alloc_state ~root_ref
            ~make_inst:(fun x y z -> MUL (x, y, z)) ~op1 ~op2 ~res:r
      | DIV (op1, op2, r) ->
          spill_bin_op ~asm_acc ~spilled_reg_offsets ~reg_alloc_state ~root_ref
            ~make_inst:(fun x y z -> DIV (x, y, z)) ~op1 ~op2 ~res:r
      | MOD (op1, op2, r) ->
          spill_bin_op ~asm_acc ~spilled_reg_offsets ~reg_alloc_state ~root_ref
            ~make_inst:(fun x y z -> MOD (x, y, z)) ~op1 ~op2 ~res:r
      | JE (op1, op2, label) ->
          let make_inst op_list res_opt =
            match (op_list, res_opt) with
            | ([o1; o2], None) ->
                JE (o1, o2, label)
            | _ ->
                assert false
          in
          spill_instruction ~asm_acc ~spilled_reg_offsets ~reg_alloc_state ~root_ref
            ~make_inst ~ops:[op1; op2] ~res_opt:None
      | JL (op1, op2, label) ->
          let make_inst op_list res_opt =
            match (op_list, res_opt) with
            | ([o1; o2], None) ->
                JL (o1, o2, label)
            | _ ->
                assert false
          in
          spill_instruction ~asm_acc ~spilled_reg_offsets ~reg_alloc_state ~root_ref
            ~make_inst ~ops:[op1; op2] ~res_opt:None
      | LOAD (reg1, reg2) ->
          let make_inst op_list res_opt =
            match (op_list, res_opt) with
            | ([Reg r1], Some r2) ->
                LOAD (r1, r2)
            | _ ->
                assert false
          in
          spill_instruction ~asm_acc ~spilled_reg_offsets ~reg_alloc_state ~root_ref
            ~make_inst ~ops:[Reg reg1] ~res_opt:(Some reg2)
      | CALL_VS2 (routine, op_list, result_reg) ->
          let make_inst ops res_opt =
            match res_opt with
            | Some res ->
                CALL_VS2 (routine, ops, res)
            | None ->
                assert false
          in
          spill_instruction ~asm_acc ~spilled_reg_offsets ~reg_alloc_state ~root_ref
            ~make_inst ~ops:op_list ~res_opt:(Some result_reg)
      | STORE (reg1, op2) ->
          let make_inst op_list res_opt =
            match (op_list, res_opt) with
            | ([o2], Some r1) ->
                STORE (r1, o2)
            | _ ->
                assert false
          in
          spill_instruction ~asm_acc ~spilled_reg_offsets ~reg_alloc_state ~root_ref
            ~make_inst ~ops:[op2] ~res_opt:(Some reg1)
      | RET op ->
          begin match op with
          | Const _ ->
              (reg_alloc_state,
                RET op ::
                CALL_VS2 (Const (AsmRoutine "zml_unregister_root"), [Reg root_ref], root_ref) ::
                asm_acc)
          | Reg r ->
              let (reg_alloc_state, op, load_asm) =
                inject_loads ~spilled_reg_offsets:spilled_reg_offsets ~reg_alloc_state ~reg:r ~root_ref
              in
              (reg_alloc_state,
                RET op ::
                CALL_VS2 (Const (AsmRoutine "zml_unregister_root"), [Reg root_ref], root_ref) ::
                (List.rev_append load_asm asm_acc))
          end
      | (JUMP label as inst) | (Label label as inst) ->
          (reg_alloc_state, inst :: asm_acc))
    (reg_alloc_state, [])
    asm
  in
  header @ (List.rev modified_asm)


(* Allocate registers for the block of assembly.  The assembly is modified
 * to reflect the register allocation; if necessary, the assembly is also
 * modified to spill registers to a heap-allocated value array. *)
let rec alloc_registers
  ?(spilled_regs=VRegSet.empty)   (* Virtual registers which have been spilled previously *)
  (precolored_regs : VReg.t list) (* Virtual registers which must be assigned to specific zasm regs *)
  (asm : VReg.t t list)           (* Virtual asm to be analyzed *)
  (reg_alloc_state : int)         (* Describes the set of virtual registers used by the asm *)
    : ZReg.t t list =
  let (modified_asm, precolored_regs) =
    if VRegSet.is_empty spilled_regs then
      (asm, precolored_regs)
    else
      (* The spill_to_heap implementation uses an additional register to store a reference
       * to the spill array, and this reference is maintained across the entire function body.
       * It doesn't make sense to ever consider spilling this register, so we'll precolor it. *)
      let (reg_alloc_state, root_ref) = VRegState.next reg_alloc_state in
      (spill_to_heap spilled_regs root_ref reg_alloc_state asm, precolored_regs @ [root_ref])
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
      let spilled_regs = VRegSet.union spilled_regs new_spilled_regs in
      alloc_registers ~spilled_regs precolored_regs asm reg_alloc_state


(* Compile a function, yielding an assembly listing for the function body. *)
let compile (f_args : var_t list) (f_body : Function.expr_t) : ZReg.t t list =
  let virtual_args, virtual_asm, vreg_alloc_state = compile_virtual f_args f_body in
  alloc_registers virtual_args virtual_asm vreg_alloc_state


