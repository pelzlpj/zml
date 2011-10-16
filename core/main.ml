
let parse filename =
  let ast =
    let in_ch = open_in filename in
    let x = Parser.expr Lexer.token (Lexing.from_channel in_ch) in
    let () = close_in in_ch in
    x
  in
  (* print_endline (Syntax.print_ast ast) *)
  let typed_ast = Typing.annotate Typing.SMap.empty ast in
  let constraints = Typing.compute_constraints [] [typed_ast] in
  Typing.print_constraints constraints


let _ = parse Sys.argv.(1)

