(* Z-Machine assembly details which may be specific to the 'zapf' assembler.
 *
 * For the moment, zml is generating Z-Machine assembly in a format compatible
 * with the 'zapf' compiler.  This may be temporary... it probably makes sense
 * to integrate an assembler into zml.  Consequently, the zapf dependencies
 * are getting segregated here.
 *)

open Printf
open Zasm


let string_of_operand_prog (program : Function.program_t) op =
  match op with
  | Const (MappedRoutine f_id) -> asm_fun_name_of_id program f_id
  | Const (AsmRoutine s)       -> s
  | Const (ConstNum i)         -> string_of_int i  (* Does Zapf accept this? *)
  | Reg reg                    -> (ZReg.string_of reg)


(* Serialize a list of assembly instructions to a string. *)
let rec string_of_asm
  ?(acc=[])                       (* accumulator for the result *)
  (program : Function.program_t)  (* description of entire program (functions + entry point) *)
  (asm : ZReg.t Zasm.t list)      (* instructions to be serialized *)
    : string =
  let string_of_operand op = string_of_operand_prog program op in
  match asm with
  | [] ->
      String.concat "\n" (List.rev acc)
  | inst :: tail ->
      let s =
        match inst with
        | ADD (a, b, r) ->
            sprintf "  add %s %s -> %s" (string_of_operand a) (string_of_operand b) (ZReg.string_of r)
        | SUB (a, b, r) ->
            sprintf "  sub %s %s -> %s" (string_of_operand a) (string_of_operand b) (ZReg.string_of r)
        | MUL (a, b, r) ->
            sprintf "  mul %s %s -> %s" (string_of_operand a) (string_of_operand b) (ZReg.string_of r)
        | DIV (a, b, r) ->
            sprintf "  div %s %s -> %s" (string_of_operand a) (string_of_operand b) (ZReg.string_of r)
        | MOD (a, b, r) ->
            sprintf "  mod %s %s -> %s" (string_of_operand a) (string_of_operand b) (ZReg.string_of r)
        | JE (a, b, lb) ->
            sprintf "  je %s %s ?label%d" (string_of_operand a) (string_of_operand b) lb
        | JL (a, b, lb) ->
            sprintf "  jl %s %s ?label%d" (string_of_operand a) (string_of_operand b) lb
        | JUMP lb ->
            (* workaround for zapf-0.3 parser bug: need to omit question mark before the label. *)
            sprintf "  jump label%d" lb
        | LOAD (r1, r2) ->
            sprintf "  load %s -> %s" (ZReg.string_of r1) (ZReg.string_of r2)
        | STORE (r, a) ->
            sprintf "  store '%s %s" (ZReg.string_of r) (string_of_operand a)
        | CALL_VS2 (f, reg_args, r) ->
            sprintf "  call_vs2 %s %s -> %s"
              (string_of_operand f)
              (String.concat " " (List.map string_of_operand reg_args))
              (ZReg.string_of r)
        | RET a ->
            sprintf "  ret %s" (string_of_operand a)
        | Label lb ->
            sprintf "label%d:" lb
      in
      string_of_asm ~acc:(s :: acc) program tail


(* Compile a function and serialize it to Zapf-compatible assembly. *)
let string_of_function
  (program : Function.program_t)  (* description of entire program (functions + entry point) *)
  (f_id : SPVar.t)                (* identifier for function to be compiled *)
    : string =
  let f_def = SPVMap.find f_id program.Function.functions in
  match f_def.Function.f_impl with
  | Function.NativeFunc (f_args, f_body) ->
      let asm = compile f_args f_body in
      let local_var_names = (List.map (sprintf "r%d") (list_range 15)) in
      let local_vars_str = String.concat ", " local_var_names in
      let funct_header = sprintf ".FUNCT %s, %s\n"
        (asm_fun_name_of_id program f_id)
        local_vars_str
      in
      let funct_body = string_of_asm program asm in
      funct_header ^ funct_body
  | Function.ExtFunc _ ->
      ""


(* Compile all functions, and serialize them to Zapf-compatible assembly. *)
let string_of_program (program : Function.program_t) : string =
  (* Skip over the external function declarations... *)
  let f_strings = Function.SPVMap.fold
    (fun f_id f_def acc ->
      match f_def.Function.f_impl with
      | Function.NativeFunc _ -> 
          (string_of_function program f_id) :: acc
      | Function.ExtFunc _ ->
          acc)
    program.Function.functions
    []
  in
  String.concat "\n\n" f_strings

