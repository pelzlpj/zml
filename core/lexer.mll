(******************************************************************************
 *  ZML -- an ML compiler targeting interactive fiction virtual machines
 *  Copyright (C) 2011-2012 Paul Pelzl
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License, version 2,
 *  as published by the Free Software Foundation.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 *  Please send bug reports, patches, etc. to Paul Pelzl at 
 *  <pelzlpj@gmail.com>.
 ******************************************************************************)


{
  open Parser

  let create_hashtable assoc =
    let table = Hashtbl.create 10 in
    List.iter (fun (key, value) -> Hashtbl.add table key value) assoc;
    table

  let keyword_tokens = [
    "if"       , IF;
    "then"     , THEN;
    "else"     , ELSE;
    "let"      , LET;
    "rec"      , REC;
    "in"       , IN;
    "not"      , NOT;
    "mod"      , MOD;
    "true"     , BOOL(true);
    "false"    , BOOL(false);
    "external" , EXTERNAL;
    "unit"     , TYPE_UNIT;
    "bool"     , TYPE_BOOL;
    "int"      , TYPE_INT;
  ]

  let keyword_table = create_hashtable keyword_tokens
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
  | ws+
    { token lexbuf }
  | '('
    { LPAREN }
  | ')'
    { RPAREN }
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
  | ":"
    { COLON }
  | ";"
    { SEMI }
  | "->"
    { TYPE_ARROW }
  | lower (lower|upper|digit|'_')*
    { let s = Lexing.lexeme lexbuf in
      try Hashtbl.find keyword_table s
      with Not_found -> IDENT(Lexing.lexeme lexbuf) }
  | "\"" ("\\\""|[^'"'])* "\""
    { let lexeme = Lexing.lexeme lexbuf in
      let quoted_content = String.sub lexeme 1 ((String.length lexeme) - 2) in
      STRING_LITERAL(quoted_content) }
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
 

