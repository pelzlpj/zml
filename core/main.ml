
let parse filename =
  let ast =
    let in_ch = open_in filename in
    let x = Parser.exp Lexer.token (Lexing.from_channel in_ch) in
    let () = close_in in_ch in
    x
  in
  print_endline (Syntax.print_ast ast)


let _ = parse Sys.argv.(1)

