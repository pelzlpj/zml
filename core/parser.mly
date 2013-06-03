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

(* Convenience function for generating the expression tree associated with binary
 * operator application. *)
let untyped_binary_op (op_function : string) left_expr right_expr =
  let op_expr = untyped_expr_rhs 2 (Var op_function) in
  let left_apply_expr = untyped_expr (Apply (op_expr, left_expr)) {
    fr_start = Parsing.rhs_start_pos 1;
    fr_end   = Parsing.rhs_end_pos 2
  } in
  untyped_expr_sym (Apply (left_apply_expr, right_expr))


(* When the user provides type expressions, we use the following hash table to associate
 * named type variables with abstract type variables. *)
let tvar_map = Hashtbl.create 50

let make_named_tvar (ident : string) : TypeVar.t =
  try
    Hashtbl.find tvar_map ident
  with Not_found ->
    (* It's possible that "fresh ()" will return a type variable which
     * collides with a variable generated during type inference.  This isn't
     * a problem, because in the context of the parser these type variables
     * are *always* universally quantified. *)
    let tvar = TypeVar.fresh () in
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
    { untyped_expr_sym (Let (Id.mktmp (), $1, $3)) }

expr:
  | simple_expr_list
    { $1 }
  | LET IDENT ident_list EQ expr IN seq_expr
    { let lambda_chain = List.fold_left
        (fun acc ident ->
          (* FIXME: parser_info is a complete fiction.  I guess the
           * ident_list carries the correct information? *)
          { expr = Lambda (ident, acc); parser_info = acc.parser_info })
        $5
        $3
      in
      untyped_expr_sym (Let ($2, lambda_chain, $7)) }
  | LET REC IDENT ident_list EQ expr IN seq_expr
    { let lambda_chain = List.fold_left
        (fun acc ident ->
          (* FIXME: parser_info is a complete fiction.  I guess the
           * ident_list carries the correct information? *)
          { expr = Lambda (ident, acc); parser_info = acc.parser_info })
        $6
        $4
      in
      untyped_expr_sym (LetRec ($3, lambda_chain, $8)) }
  | EXTERNAL IDENT COLON type_expr EQ STRING_LITERAL IN seq_expr
    { typed_expr_sym (External ($2, $4, $6, $8)) $4 }
  | IF expr THEN expr ELSE expr
    { untyped_expr_sym (If ($2, $4, $6)) }
  | NOT expr
    %prec prec_unary_minus
    { let op_expr = untyped_expr_rhs 1 (Var Builtins.logic_not) in
      untyped_expr_sym (Apply (op_expr, $2)) }
  | MINUS expr
    %prec prec_unary_minus
    { let op_expr = untyped_expr_rhs 1 (Var Builtins.neg) in
      untyped_expr_sym (Apply (op_expr, $2)) }
  | expr PLUS expr
    { untyped_binary_op Builtins.add $1 $3 }
  | expr MINUS expr
    { untyped_binary_op Builtins.sub $1 $3 }
  | expr STAR expr
    { untyped_binary_op Builtins.mul $1 $3 }
  | expr SLASH expr
    { untyped_binary_op Builtins.div $1 $3 }
  | expr MOD expr
    { untyped_binary_op Builtins.modulus $1 $3 }
  | expr EQ expr
    { untyped_binary_op Builtins.eq $1 $3 }
  | expr NEQ expr
    { untyped_binary_op Builtins.neq $1 $3 }
  | expr LEQ expr
    { untyped_binary_op Builtins.leq $1 $3 }
  | expr GEQ expr
    { untyped_binary_op Builtins.geq $1 $3 }
  | expr LT expr
    { untyped_binary_op Builtins.less $1 $3 }
  | expr GT expr
    { untyped_binary_op Builtins.greater $1 $3 }
  | simple_expr DOT LPAREN seq_expr RPAREN LARROW expr
    { let op_expr         = untyped_expr_rhs 6 (Var Builtins.array_set) in
      let apply_arg1_expr = untyped_expr (Apply (op_expr, $1)) {
        fr_start = Parsing.rhs_start_pos 1;
        fr_end   = Parsing.rhs_end_pos 2
      } in
      let apply_arg2_expr = untyped_expr (Apply (apply_arg1_expr, $4)) {
        fr_start = Parsing.rhs_start_pos 1;
        fr_end   = Parsing.rhs_end_pos 5
      } in
      untyped_expr_sym (Apply (apply_arg2_expr, $7)) }
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
    { let op_expr         = untyped_expr_rhs 2 (Var Builtins.array_get) in
      let apply_arg1_expr = untyped_expr (Apply (op_expr, $1)) {
        fr_start = Parsing.rhs_start_pos 1;
        fr_end   = Parsing.rhs_end_pos   2
      } in
      untyped_expr_sym (Apply (apply_arg1_expr, $4)) }


simple_expr_list:
  | simple_expr_list simple_expr
    { untyped_expr_sym (Apply ($1, $2)) }
  | simple_expr
    { $1 }


ident_list:
  | ident_list IDENT
    { $2 :: $1 }
  | /* empty */
    { [] }


type_expr:
  | QUOTE IDENT
    { let tv = make_named_tvar $2 in
      Type.ForAll (Type.TVSet.singleton tv, Type.Var tv) }
  | LPAREN type_expr RPAREN
    { $2 }
  | type_expr TYPE_ARROW type_expr
    { match ($1, $3) with
      | (Type.ForAll (left_set, left_tp), Type.ForAll (right_set, right_tp)) ->
          Type.ForAll (Type.TVSet.union left_set right_set, Type.Arrow (left_tp, right_tp)) }
  | TYPE_UNIT
    { Type.ForAll (Type.TVSet.empty, Type.Unit) }
  | TYPE_BOOL
    { Type.ForAll (Type.TVSet.empty, Type.Bool) }
  | TYPE_INT
    { Type.ForAll (Type.TVSet.empty, Type.Int) }
  | type_expr TYPE_ARRAY
    { match $1 with
      | Type.ForAll (tv_set, param_tp) ->
          Type.ForAll (tv_set, Type.Array param_tp) }


