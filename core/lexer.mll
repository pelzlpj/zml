(*  zml -- an ML compiler for the Z-Machine
 *  Copyright (C) 2009 Paul Pelzl
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License, Version 2,
 *  as published by the Free Software Foundation.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 *  Please send bug reports, patches, etc. to Paul Pelzl at 
 *  <pelzlpj@gmail.com>.
 *)

{
  open Parser

  let create_hashtable assoc =
    let table = Hashtbl.create 10 in
    List.iter (fun (key, value) -> Hashtbl.add table key value) assoc;
    table

  let keyword_assoc = [
    "if", IF;
    "then", THEN;
    "else", ELSE;
    "let", LET;
    "rec", REC;
  ]

  let keyword_table = create_hashtable keyword_assoc
}


let ws      = [' ' '\t']
let digit   = ['0'-'9']
let lower   = ['a'-'z']
let upper   = ['A'-'Z']
let newline = ('\n' | '\r' | "\r\n")


rule token = parse
  | "(*"
    { comment lexbuf;           (* Special handling to support nested comments *)
      token lexbuf }
  | newline
    { Lexing.new_line lexbuf;   (* Track line numbers during lexing, for better error reporting *)
      token lexbuf }
  | space+
    { token lexbuf }
  | '('
    { LPAREN }
  | ')'
    { RPAREN }
  | "true"
    { BOOL(true) }
  | "false"
    { BOOL(false) }
  | "not"
    { NOT }
  | digit+
    { INT(int_of_string (Lexing.lexeme lexbuf)) }
  | '-'
    { MINUS }
  | '+'
    { PLUS }
  | '*'
    { STAR }
  | '/'
    { SLASH }
  | "mod"
    { MOD }
  | '='
    { EQ }
  | "<>"
    { NEQ }
  | "<="
    { LEQ }
  | ">="
    { GEQ }
  | "<"
    { LT }
  | ">"
    { GT }
  | ";"
    { SEMI }
  | lower (lower|upper|digit|'_')*
    { let s = Lexing.lexeme lexbuf in
      try Hashtbl.find keyword_table s
      with Not_found -> LIDENT(Lexing.lexeme lexbuf) }
  | eof
    { EOF }
  | _
    { let start_pos = Lexing.lexeme_start_p lexbuf in
      let line_ofs = start_pos.Lexing.pos_cnum - start_pos.Lexing.pos_bol in
      failwith (Printf.sprintf "Unknown token %s at line %u, char %u."
                  (Lexing.lexeme lexbuf) 
                  start_pos.Lexing.pos_lnum
                  line_ofs) }
and comment = parse
  | "*)"
    { () }
  | "(*"
    { comment lexbuf;
      comment lexbuf }
  | eof
    { Printf.fprintf stderr "Warning: unterminated comment.\n" }
  | _
    { comment lexbuf }
 

