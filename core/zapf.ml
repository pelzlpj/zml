(* Z-Machine assembly details which may be specific to the 'zapf' assembler.
 *
 * For the moment, zml is generating Z-Machine assembly in a format compatible
 * with the 'zapf' compiler.  This may be temporary... it probably makes sense
 * to integrate an assembler into zml.  Consequently, the zapf dependencies
 * are getting segregated here.
 *)

open Printf
open Zasm


let string_of_operand op =
  match op with
  | Reg r ->
      sprintf "r%d" r
  | Const c ->
      sprintf "%d" c


(* Serialize a list of assembly instructions to a string. *)
let rec string_of_asm
  ?(acc=[])                 (* accumulator for the result *)
  (program : Function.t)    (* description of entire program (functions + entry point) *)
  (asm : Zasm.t list)       (* instructions to be serialized *)
    : string =
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
            (* workaround for zapf-0.3 parser bug: need to omit question mark before the label. *)
            sprintf "  jump label%d" lb
        | LOAD (r1, r2) ->
            sprintf "  load r%d -> r%d" r1 r2
        | STORE (r, a) ->
            sprintf "  store 'r%d %s" r (string_of_operand a)
        | CALL_VS2 (f, reg_args, r) ->
            sprintf "  call_vs2 %s %s -> r%d"
              (asm_fun_name_of_id program f)
              (String.concat " " (List.map (sprintf "r%d") reg_args))
              r
        | RET a ->
            sprintf "  ret %s" (string_of_operand a)
        | Label lb ->
            sprintf "label%d:" lb
      in
      string_of_asm ~acc:(s :: acc) program tail


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


(* Compile a function and serialize it to Zapf-compatible assembly. *)
let string_of_function
  (program : Function.t)  (* description of entire program (functions + entry point) *)
  (f_id : var_t)          (* identifier for function to be compiled *)
    : string =
  let f_def = VMap.find f_id program.Function.functions in
  let asm = compile_virtual f_def in
  let local_var_names = List.map (sprintf "r%d") (list_range 15) in
  let local_vars_str = String.concat ", " local_var_names in
  let funct_header = sprintf ".FUNCT %s, %s\n"
    (asm_fun_name_of_id program f_id)
    local_vars_str
  in
  let funct_body = string_of_asm program asm in
  funct_header ^ funct_body


(* Compile all functions, and serialize them to Zapf-compatible assembly. *)
let string_of_program (program : Function.t) : string =
  let f_strings = Function.VMap.fold
    (fun f_id f_def acc -> (string_of_function program f_id) :: acc)
    program.Function.functions
    []
  in
  String.concat "\n\n" f_strings

