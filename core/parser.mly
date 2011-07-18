%{
(*  zml -- an ML compiler for the Z-Machine
 *  Copyright (C) 2009-2011 Paul Pelzl
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

open Syntax
%}


%token IF
%token THEN
%token ELSE
%token LET
%token REC
%token IN
%token LPAREN
%token RPAREN
%token <bool> BOOL
%token NOT
%token <int> INT
%token MINUS
%token PLUS
%token STAR
%token SLASH
%token MOD
%token EQ
%token NEQ
%token LEQ
%token GEQ
%token LT
%token GT
%token SEMI
%token <string> IDENT
%token EOF


/* Precedence rules. */

%nonassoc IN
%nonassoc below_SEMI
%nonassoc SEMI
%nonassoc LET
%nonassoc THEN
%nonassoc ELSE
%left     EQ LT GT NEQ LEQ GEQ
%left     PLUS MINUS
%left     STAR SLASH MOD
%nonassoc prec_unary_minus


/* The entry point must be an expression of the given type. */

%type <Syntax.t> exp
%start exp

%%

/* Grammar definitions follow. */

exp:
  | LPAREN exp RPAREN
    { $2 }
  | LPAREN RPAREN
    { Unit }
  | BOOL
    { Bool ($1) }
  | INT
    { Int ($1) }
  | IDENT
    { Var ($1) }
  | NOT exp
    { Not ($2) }
  | MINUS exp
    %prec prec_unary_minus
    { Neg ($2) }
  | exp PLUS exp
    { Add ($1, $3) }
  | exp MINUS exp
    { Sub ($1, $3) }
  | exp STAR exp
    { Mul ($1, $3) }
  | exp SLASH exp
    { Div ($1, $3) }
  | exp MOD exp
    { Mod ($1, $3) }
  | exp EQ exp
    { Eq ($1, $3) }
  | exp NEQ exp
    { Not (Eq ($1, $3)) }
  | exp LEQ exp
    { Not (Less ($3, $1)) }
  | exp GEQ exp
    { Not (Less ($1, $3)) }
  | exp LT exp
    { Less ($1, $3) }
  | exp GT exp
    { Less ($3, $1) }
  | IF exp THEN exp ELSE exp
    { If ($2, $4, $6) }
  | LET IDENT EQ exp IN exp
    { Let ($2, $4, $6) }
  | LET REC fundef IN exp
    { LetRec ($3, $5) }
  | exp SEMI exp
    { Let (Id.mktmp (), $1, $3) }
  | error
    { let spos = Parsing.symbol_start_pos () in
      let epos = Parsing.symbol_end_pos () in
      let sofs = spos.Lexing.pos_cnum - spos.Lexing.pos_bol
      and eofs = epos.Lexing.pos_cnum - epos.Lexing.pos_bol in
      failwith (Printf.sprintf 
        "Parse error, line %u char %u through line %u char %u."
        spos.Lexing.pos_lnum sofs epos.Lexing.pos_lnum eofs) }
        
fundef:
  | IDENT funargs EQ exp
    { {fun_name = $1; fun_args = $2; fun_body = $4} }
    
funargs:
  | IDENT funargs
    { $1 :: $2 }
  | IDENT
    { [$1] }
  


