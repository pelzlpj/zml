
open Printf

module VarID = Normal.VarID
module VMap  = Normal.VMap
type var_t   = Normal.var_t

(* Identifiers for Z-Machine variables *)
type reg_t   = int

(* Identifiers for labels placed within a function body *)
type label_t = int

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


let string_of_operand op =
  match op with
  | Reg r ->
      sprintf "r%d" r
  | Const c ->
      sprintf "%d" c


let rec to_string ?(acc=[]) (asm : t list) =
  match asm with
  | [] ->
      String.concat "\n" (List.rev acc)
  | inst :: tail ->
      let s =
        match inst with
        | ADD (a, b, r) ->
            sprintf "  add %s %s -> r%d" (string_of_operand a) (string_of_operand b) r
        | SUB (a, b, r) ->
            sprintf "  sub %s %s -> r%d" (string_of_operand a) (string_of_operand b) r
        | MUL (a, b, r) ->
            sprintf "  mul %s %s -> r%d" (string_of_operand a) (string_of_operand b) r
        | DIV (a, b, r) ->
            sprintf "  div %s %s -> r%d" (string_of_operand a) (string_of_operand b) r
        | MOD (a, b, r) ->
            sprintf "  mod %s %s -> r%d" (string_of_operand a) (string_of_operand b) r
        | JE (a, b, lb) ->
            sprintf "  je %s %s ?label%d" (string_of_operand a) (string_of_operand b) lb
        | JL (a, b, lb) ->
            sprintf "  jl %s %s ?label%d" (string_of_operand a) (string_of_operand b) lb
        | JUMP lb ->
            sprintf "  jump ?label%d" lb
        | LOAD (r1, r2) ->
            sprintf "  load r%d -> r%d" r1 r2
        | STORE (r, a) ->
            sprintf "  store 'r%d %s" r (string_of_operand a)
        | CALL_VS2 (f, reg_args, r) ->
            sprintf "  call_vs2 function_%s %s -> r%d"
              (VarID.to_string f) 
              (String.concat " " (List.map (sprintf "r%d") reg_args))
              r
        | RET a ->
            sprintf "  ret %s" (string_of_operand a)
        | Label lb ->
            sprintf "label%d:" lb
      in
      to_string ~acc:(s :: acc) tail


type state_t = {
  reg_of_var : int VMap.t;    (* Maps Normal.t variables to Z-Machine registers *)
  reg_count  : int;           (* Number of registers consumed *)
  label_count: int            (* Number of labels emitted *)
}

let rec compile_virtual_aux
  (state : state_t)           (* Compilation context *)
  (expr : Function.expr_t)    (* Expression to be compiled *)
    : (
      state_t *   (* New context *)
      t list *    (* List of instructions for the expression *)
      int         (* Register which contains expression result after instruction evaluation *)
    ) =
  match expr with
  | Function.Unit ->
      (* For now we're treating unit as integer zero.  It shouldn't matter. *)
      compile_virtual_aux state (Function.Int 0)
  | Function.Int i -> (
      {state with reg_count = state.reg_count + 1},
      [STORE (state.reg_count, Const i)],
      state.reg_count
    )
  | Function.Add (a, b) ->
      compile_virtual_binary_int state (fun x y z -> ADD (x, y, z)) a b
  | Function.Sub (a, b) ->
      compile_virtual_binary_int state (fun x y z -> SUB (x, y, z)) a b
  | Function.Mul (a, b) ->
      compile_virtual_binary_int state (fun x y z -> MUL (x, y, z)) a b
  | Function.Div (a, b) ->
      compile_virtual_binary_int state (fun x y z -> DIV (x, y, z)) a b
  | Function.Mod (a, b) ->
      compile_virtual_binary_int state (fun x y z -> MOD (x, y, z)) a b
  | Function.Neg a ->
      (* Negation is implemented as subtraction from zero. *)
      ({state with reg_count = state.reg_count + 1},
      [SUB ((Const 0), (Reg (VMap.find a state.reg_of_var)), state.reg_count)],
      state.reg_count)
  | Function.IfEq (a, b, e1, e2) ->
      compile_virtual_if state true a b e1 e2
  | Function.IfLess (a, b, e1, e2) ->
      compile_virtual_if state false a b e1 e2
  | Function.Var a ->
      (state, [], VMap.find a state.reg_of_var)
  | Function.Let (a, e1, e2) ->
      (* "let" just leads to emitting instructions for [e1] prior to [e2],
       * with the additional constraint that [a] becomes an alias for the
       * [e1] result register while compiling [e2]. *)
      let (state, head, head_reg) = compile_virtual_aux state e1 in
      let new_binding_state = {state with reg_of_var = VMap.add a head_reg state.reg_of_var} in
      let (state, tail, tail_reg) = compile_virtual_aux new_binding_state e2 in
      (state, head @ tail, tail_reg)
  | Function.Apply (g, g_args) ->
      let arg_regs = List.map (fun v -> VMap.find v state.reg_of_var) g_args in (
        {state with reg_count = state.reg_count + 1},
        [CALL_VS2 (g, arg_regs, state.reg_count)],
        state.reg_count
      )

(* Compile a binary integer operation. *)
and compile_virtual_binary_int state f a b = (
  {state with reg_count = state.reg_count + 1},
  [f (Reg (VMap.find a state.reg_of_var)) (Reg (VMap.find b state.reg_of_var)) state.reg_count],
  state.reg_count
)

(* Compile an IfEq or IfLess form. *)
and compile_virtual_if state is_cmp_equality a b e1 e2 =
  (* Compiles down to assembly of this form:
   *    je a b ?true_label
   *    (code for e2)
   *    load e2_result_reg -> result_reg
   *    jump ?exit_label
   * true_label:
   *    (code_for_e1)
   *    load e1_result_reg -> result_reg
   * exit_label:
   *)    
  let (state, true_branch, true_reg)   = compile_virtual_aux state e1 in
  let (state, false_branch, false_reg) = compile_virtual_aux state e2 in
  let true_label = state.label_count in
  let exit_label = true_label + 1 in
  let result_reg = state.reg_count in
  let branch_inst =
    let a_reg = Reg (VMap.find a state.reg_of_var) in
    let b_reg = Reg (VMap.find b state.reg_of_var) in
    if is_cmp_equality then
      [JE (a_reg, b_reg, true_label)]
    else
      [JL (a_reg, b_reg, true_label)]
  in
  let false_cleanup = [
    LOAD (false_reg, state.reg_count);
    JUMP exit_label
  ] in
  let true_cleanup = [
    LOAD (true_reg, state.reg_count)
  ] in ( 
    {state with label_count = exit_label + 1; reg_count = result_reg + 1},
    (branch_inst @
      false_branch @ false_cleanup @
      [Label true_label] @
      true_branch @ true_cleanup @
      [Label exit_label]),
    result_reg
  )


(* Compile a function to "virtual" Z5 assembly.  This is Z-machine assembly
 * with an infinite number of registers (aka "local variables") available. *)
let compile_virtual (f : Function.function_t) : t list =
  (* call_vs2 supports 0 through 7 arguments.  Implementing functions with
   * more than seven arguments will require heap-allocating a reference array
   * as storage for the extra args. *)
  let call_vs2_max_args = 7 in
  let () = assert (List.length f.Function.f_args <= call_vs2_max_args) in
  let init_state = List.fold_left
    (fun acc arg -> {acc with
       reg_of_var = VMap.add arg acc.reg_count acc.reg_of_var;
       reg_count  = acc.reg_count + 1
      })
    {reg_of_var = VMap.empty; reg_count = 0; label_count = 0}
    f.Function.f_args
  in
  let (_, assembly, result_reg) = compile_virtual_aux init_state f.Function.f_body in
  assembly @ [RET (Reg result_reg)]


