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
    (* let () = print_endline s in *)
    let program = Function.extract_functions normal in
    (* let s = Function.string_of_program program in *)
    let ref_program = RefTracking.insert_ref_management program in
    (* let s = RefTracking.string_of_program ref_program in *)
    (* let () = print_endline s in *)
    let ir = IR.drop_ids ref_program in
    let zapf_asm = Zapf.string_of_program ir in
    print_endline zapf_asm

    (* let s = Function.to_string func_normal in *)
    (*let () = print_endline s in
    () *)
  with AlgW.Unification_failure constr ->
    let error_range = constr.AlgW.error_info.ParserMeta.range in
    let () = Printf.printf "Typing error in range %d:%d-%d:%d\n"
      error_range.ParserMeta.fr_start.Lexing.pos_lnum
      (error_range.ParserMeta.fr_start.Lexing.pos_cnum -
        error_range.ParserMeta.fr_start.Lexing.pos_bol + 1)
      error_range.ParserMeta.fr_end.Lexing.pos_lnum
      (error_range.ParserMeta.fr_end.Lexing.pos_cnum -
        error_range.ParserMeta.fr_end.Lexing.pos_bol + 1)
    in
    let (ctx, left_type) =
      Type.local_rename_typevars Type.empty_rename_ctx constr.AlgW.left_type
    in
    let (ctx, right_type) =
      Type.local_rename_typevars ctx constr.AlgW.right_type
    in
    let () = Printf.printf "This expression has type\n    %s\n" (Type.string_of_type left_type) in
    Printf.printf "An expression was expected of type\n    %s\n" (Type.string_of_type right_type)


let _ =
  let () = Printexc.record_backtrace true in
  parse Sys.argv.(1)

