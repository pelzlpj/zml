%{
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

let typed_expr_sym expr type_annot = typed_expr expr type_annot (symbol_range ())

(* When the user provides type expressions, we use the following hash table to assign
 * a unique integer to every unique type variable identifier. *)
let tvar_map   = Hashtbl.create 50
let tvar_count = ref 0

let make_tvar ident =
  try
    Hashtbl.find tvar_map ident
  with Not_found ->
    let tvar = !tvar_count in
    let () = incr tvar_count in
    let () = Hashtbl.add tvar_map ident tvar in
    tvar

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
%token COLON
%token DOT
%token LARROW
%token <string> IDENT
%token <string> STRING_LITERAL
%token EXTERNAL
%token TYPE_UNIT
%token TYPE_BOOL
%token TYPE_INT
%token TYPE_ARROW
%token TYPE_ARRAY
%token QUOTE
%token EOF


/* Precedence rules. */

%left     TYPE_ARROW
%nonassoc IN
%nonassoc below_SEMI
%nonassoc SEMI
%nonassoc LET
%nonassoc THEN
%nonassoc ELSE
%nonassoc LARROW
%left     EQ LT GT NEQ LEQ GEQ
%left     PLUS MINUS
%left     STAR SLASH MOD
%nonassoc prec_unary_minus

/* The starting tokens of simple_expr have highest precedence. */
%nonassoc LPAREN BOOL INT IDENT TYPE_ARRAY


/* The entry point must be an expression of the given type. */
%type <Syntax.t> expr
%start expr

%%

/* Grammar definitions follow. */

seq_expr:
  | expr
    %prec below_SEMI
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
  | EXTERNAL IDENT COLON type_expr EQ STRING_LITERAL IN seq_expr
    { typed_expr_sym (External ($2, $4, $6, $8)) $4 }
  | IF expr THEN expr ELSE expr
    { untyped_expr_sym (If ($2, $4, $6)) }
  | NOT expr
    %prec prec_unary_minus
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
  | simple_expr DOT LPAREN seq_expr RPAREN LARROW expr
    { untyped_expr_sym (ArraySet ($1, $4, $7)) }
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
  | LPAREN seq_expr COLON type_expr RPAREN
    { typed_expr_sym ($2).expr $4 }
  | LPAREN RPAREN
    { untyped_expr_sym Unit }
  | BOOL
    { untyped_expr_sym (Bool ($1)) }
  | INT
    { untyped_expr_sym (Int ($1)) }
  | IDENT
    { untyped_expr_sym (Var ($1)) }
  | simple_expr DOT LPAREN seq_expr RPAREN
    { untyped_expr_sym (ArrayGet ($1, $4)) }
        

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


type_expr:
  | QUOTE IDENT
    { Type.Var (make_tvar $2) }
  | LPAREN type_expr RPAREN
    { $2 }
  | type_expr TYPE_ARROW type_expr
    { Type.Arrow ($1, $3) }
  | TYPE_UNIT
    { Type.Unit }
  | TYPE_BOOL
    { Type.Bool}
  | TYPE_INT
    { Type.Int }
  | type_expr TYPE_ARRAY
    { Type.Array $1 }


