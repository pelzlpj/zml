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

(* Gets the file range corresponding to the current parser "symbol". *)
let symbol_range () = {
  fr_start = Parsing.symbol_start_pos ();
  fr_end   = Parsing.symbol_end_pos ();
}

(* Gets the file range corresponding to the specified matching symbol on the
 * right-hand side of the current rule (indexed from 1). *)
let rhs_range n = {
  fr_start = Parsing.rhs_start_pos n;
  fr_end   = Parsing.rhs_end_pos n;
}

let untyped_expr_sym expr   = untyped_expr expr (symbol_range ())
let untyped_expr_rhs n expr = untyped_expr expr (rhs_range n)

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
%token DISAMBIGUATION


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

%type <Syntax.t> expr
%start expr

%%

/* Grammar definitions follow. */

seq_expr:
  | expr
    { $1 }
  | expr SEMI seq_expr
    { untyped_expr_sym (Let (Id.mktmp (), [], $1, $3)) }

expr:
  | simple_expr
    { $1 }
  | simple_expr simple_expr_list
    { untyped_expr_sym (Apply ($1, List.rev $2)) }
  | LET IDENT ident_list EQ expr IN seq_expr
    { untyped_expr_sym (Let ($2, List.rev $3, $5, $7)) }
  | LET REC IDENT ident_list EQ expr IN seq_expr
    { untyped_expr_sym (LetRec ($3, List.rev $4, $6, $8)) }
  | IF expr THEN expr ELSE expr
    { untyped_expr_sym (If ($2, $4, $6)) }
  | NOT expr
    { untyped_expr_sym (Not ($2)) }
  | MINUS expr
    %prec prec_unary_minus
    { untyped_expr_sym (Neg ($2)) }
  | expr PLUS expr
    { untyped_expr_sym (Add ($1, $3)) }
  | expr MINUS expr
    { untyped_expr_sym (Sub ($1, $3)) }
  | expr STAR expr
    { untyped_expr_sym (Mul ($1, $3)) }
  | expr SLASH expr
    { untyped_expr_sym (Div ($1, $3)) }
  | expr MOD expr
    { untyped_expr_sym (Mod ($1, $3)) }
  | expr EQ expr
    { untyped_expr_sym (Eq ($1, $3)) }
  | expr NEQ expr
    { untyped_expr_sym (Neq ($1, $3)) }
  | expr LEQ expr
    { untyped_expr_sym (Leq ($1, $3)) }
  | expr GEQ expr
    { untyped_expr_sym (Geq ($1, $3)) }
  | expr LT expr
    { untyped_expr_sym (Less ($1, $3)) }
  | expr GT expr
    { untyped_expr_sym (Greater ($1, $3)) }
  | error
    { let spos = Parsing.symbol_start_pos () in
      let epos = Parsing.symbol_end_pos () in
      let sofs = spos.Lexing.pos_cnum - spos.Lexing.pos_bol
      and eofs = epos.Lexing.pos_cnum - epos.Lexing.pos_bol in
      failwith (Printf.sprintf 
        "Parse error, line %u char %u through line %u char %u."
        spos.Lexing.pos_lnum sofs epos.Lexing.pos_lnum eofs) }


simple_expr:
  | LPAREN seq_expr RPAREN
    { $2 }
  | LPAREN RPAREN
    { untyped_expr_sym Unit }
  | BOOL
    { untyped_expr_sym (Bool ($1)) }
  | INT
    { untyped_expr_sym (Int ($1)) }
  | IDENT
    { untyped_expr_sym (Var ($1)) }
        

simple_expr_list:
  | simple_expr_list simple_expr
    { $2 :: $1 }
  | simple_expr
    { [$1] }


ident_list:
  | ident_list IDENT
    { $2 :: $1 }
  | /* empty */
    { [] }


