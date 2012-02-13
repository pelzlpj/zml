
open Printf

let parse filename =
  let ast =
    let in_ch = open_in filename in
    let x = Parser.expr Lexer.token (Lexing.from_channel in_ch) in
    let () = close_in in_ch in
    x
  in
  try
    let typed_ast = Typing.infer ast in
    let normal = Normal.normalize typed_ast in
    (* let s = Normal.string_of_normal normal in *)
    let program = Function.extract_functions normal in
    let s = Function.string_of_program program in
    let () = print_endline s in
    let zapf_asm = Zapf.string_of_program program in
    print_endline zapf_asm

    (* let s = Function.to_string func_normal in *)
    (*let () = print_endline s in
    () *)
  with Typing_unify.Unification_failure constr ->
    let error_range = constr.Typing_unify.error_info.Syntax.range in
    let () = Printf.printf "Typing error in range %d:%d-%d:%d\n"
      error_range.Syntax.fr_start.Lexing.pos_lnum
      (error_range.Syntax.fr_start.Lexing.pos_cnum -
        error_range.Syntax.fr_start.Lexing.pos_bol + 1)
      error_range.Syntax.fr_end.Lexing.pos_lnum
      (error_range.Syntax.fr_end.Lexing.pos_cnum -
        error_range.Syntax.fr_end.Lexing.pos_bol + 1)
    in
    let (ctx, left_type) =
      Type.local_rename_typevars Type.empty_rename_ctx constr.Typing_unify.left_type
    in
    let (ctx, right_type) =
      Type.local_rename_typevars ctx constr.Typing_unify.right_type
    in
    let () = Printf.printf "This expression has type\n    %s\n" (Type.string_of_type left_type) in
    Printf.printf "An expression was expected of type\n    %s\n" (Type.string_of_type right_type)


let _ = parse Sys.argv.(1)

