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

(* Intermediate representation.  The program is transformed into this representation as the final
 * step prior to platform-specific code generation (Z-machine, Glulx, etc.).
 *)


module ValID     = RefTracking.ValID
module RefID     = RefTracking.RefID
module VMap      = RefTracking.VMap
type sp_var_t    = RefTracking.sp_var_t
type cond_t      = RefTracking.cond_t


type binary_op_t =
  | Add   (* Integer addition *)
  | Sub   (* Integer subtraction *)
  | Mul   (* Integer multiplication *)
  | Div   (* Integer division *)
  | Mod   (* Integer modulus *)

type unary_op_t =
  | Neg   (* Integer negation *)


type t =
  | Unit                                        (* Unit literal *)
  | Int of int                                  (* Integer constant *)
  | BinaryOp of binary_op_t * ValID.t * ValID.t (* Binary integer operation *)
  | UnaryOp of unary_op_t * ValID.t             (* Unary integer operation *)
  | Conditional of cond_t * ValID.t * ValID.t
      * t * t                                   (* Conditional form *)
  | Var of sp_var_t                             (* Bound variable reference (not a known function) *)
  | KnownFuncVar of ValID.t                     (* Known function reference *)
  | Let of sp_var_t * t * t                     (* Let binding for a variable *)
  | ApplyKnown of ValID.t * (sp_var_t list)     (* Application of "known" function *)
  | ApplyUnknown of ValID.t * (sp_var_t list)   (* Application of an "unknown" function (computed address) *)



type function_def_t =
  (* Standard function defined in ZML (function args, function body) *)
  | NativeFunc of (sp_var_t list) * t
  (* Function defined in ASM (with ASM identifier, arg count *)
  | ExtFunc of string * int


type function_t = {
  (** Name of the function (will be injected into the assembly to assist in debugging) *)
  f_name : string;
  f_impl : function_def_t
}

type program_t = {
  (* List of known functions, each indexed by a unique variable id *)
  functions   : function_t VMap.t;
  (* Function to be invoked as program entry point (with type "unit -> unit") *)
  entry_point : ValID.t
}


(* Rewrite a known-function application, recognizing built-in operators. *)
let rewrite_apply_known function_map f (args : sp_var_t list) =
  let module RT = RefTracking in
  match (VMap.find f function_map, args) with
  | ({ RT.f_impl = RT.ExtFunc (asm_name, _); _ },
      [RT.Value a; RT.Value b]) when asm_name = Builtins.asm_name_of_id Builtins.add ->
      BinaryOp (Add, a, b)
  | ({ RT.f_impl = RT.ExtFunc (asm_name, _); _ },
      [RT.Value a; RT.Value b]) when asm_name = Builtins.asm_name_of_id Builtins.sub ->
      BinaryOp (Sub, a, b)
  | ({ RT.f_impl = RT.ExtFunc (asm_name, _); _ },
      [RT.Value a; RT.Value b]) when asm_name = Builtins.asm_name_of_id Builtins.mul ->
      BinaryOp (Mul, a, b)
  | ({ RT.f_impl = RT.ExtFunc (asm_name, _); _ },
      [RT.Value a; RT.Value b]) when asm_name = Builtins.asm_name_of_id Builtins.div ->
      BinaryOp (Div, a, b)
  | ({ RT.f_impl = RT.ExtFunc (asm_name, _); _ },
      [RT.Value a; RT.Value b]) when asm_name = Builtins.asm_name_of_id Builtins.modulus ->
      BinaryOp (Mod, a, b)
  | ({ RT.f_impl = RT.ExtFunc (asm_name, _); _ },
      [RT.Value a]) when asm_name = Builtins.asm_name_of_id Builtins.neg ->
      UnaryOp (Neg, a)
  | _ ->
      ApplyKnown (f, args)


(* Rewrite a RefTracking expression into an IR expression.  The RefTracking locally-unique
 * expression IDs are dropped, and built-in operator applications are inlined into
 * first-class AST elements. *)
let rec rewrite (functions : RefTracking.function_t VMap.t) (id_expr : RefTracking.t) : t =
  let recur = rewrite functions in
  let module RT = RefTracking in
  match id_expr.RT.expr with
  | RT.Unit                             -> Unit
  | RT.Int x                            -> Int x
  | RT.Conditional (cond, a, b, e1, e2) -> Conditional (cond, a, b, recur e1, recur e2)
  | RT.Var v                            -> Var v
  | RT.KnownFuncVar v                   -> KnownFuncVar v
  | RT.Let (a, e1, e2)                  -> Let (a, recur e1, recur e2)
  | RT.ApplyKnown (f, args)             -> rewrite_apply_known functions f args
  | RT.ApplyUnknown (f, args)           -> ApplyUnknown (f, args)


(* Strip expression identifiers from the whole-program RefTracking output. *)
let drop_ids (program : RefTracking.program_t) : program_t =
  let functions =
    VMap.fold
      (fun f_id f_def acc ->
        let f_def' = {
          f_name = f_def.RefTracking.f_name;
          f_impl =
            match f_def.RefTracking.f_impl with
            | RefTracking.NativeFunc (args, body) ->
                NativeFunc (args, rewrite program.RefTracking.functions body)
            | RefTracking.ExtFunc (name, arg_count) ->
                ExtFunc (name, arg_count)
        } in
        VMap.add f_id f_def' acc)
      program.RefTracking.functions
      VMap.empty
  in
  {functions; entry_point = program.RefTracking.entry_point}


