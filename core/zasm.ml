
open Printf

module VarID = Normal.VarID
module VMap  = Normal.VMap
type var_t   = Normal.var_t

(* Identifiers for Z-Machine variables *)
type reg_t   = int

(* Identifiers for labels placed within a function body *)
type label_t = int


(* Construct an assembly function identifier from a function ID. *)
let asm_fun_name_of_id (program : Function.t) (f_id : var_t) =
  let f_def = VMap.find f_id program.Function.functions in
  let short_name = f_def.Function.f_name in
  if f_id = program.Function.entry_point then
    short_name
  else
    sprintf "%s_%s" short_name (VarID.to_int_string f_id)


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
  | JE of operand_t * operand_t * label_t
  | JL of operand_t * operand_t * label_t
  | JUMP of label_t
  | LOAD of reg_t * reg_t
  | STORE of reg_t * operand_t
  | CALL_VS2 of var_t * (reg_t list) * reg_t
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
      let arg_regs = List.map (fun v -> VMap.find v state.reg_of_var) g_args in
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
let compile_virtual (f : Function.function_t) : t list =
  (* call_vs2 supports 0 through 7 arguments.  Implementing functions with
   * more than seven arguments will require heap-allocating a reference array
   * as storage for the extra args. *)
  let call_vs2_max_args = 7 in
  let () = assert (List.length f.Function.f_args <= call_vs2_max_args) in
  let result_reg = 0 in
  let init_state = List.fold_left
    (fun acc arg -> {acc with
       reg_of_var = VMap.add arg acc.reg_count acc.reg_of_var;
       reg_count  = acc.reg_count + 1
      })
    {reg_of_var = VMap.empty; reg_count = result_reg + 1; label_count = 0}
    f.Function.f_args
  in
  let (_, assembly) = compile_virtual_aux init_state result_reg f.Function.f_body in
  assembly @ [RET (Reg result_reg)]


