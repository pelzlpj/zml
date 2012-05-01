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
type binary_op_t = RefTracking.binary_op_t
type unary_op_t  = RefTracking.unary_op_t
type cond_t      = RefTracking.cond_t


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
  | ArrayAlloc of ValID.t                       (* Construct a new array (size) *)
  | ArrayInitOne of RefID.t * ValID.t * sp_var_t(* Store a ref or value in an array, setting the
                                                    storage type to match (arr, index, val) *)
  | ArraySet of RefID.t * ValID.t * sp_var_t    (* Store a ref or value in an array (arr, index, ref) *)
  | ArrayGetVal of RefID.t * ValID.t            (* Get a value from an array (arr, index) *)
  | ArrayGetRef of RefID.t * ValID.t            (* Get a reference from an array (arr, index) *)
  | RefClone of RefID.t                         (* Create new references which points to same object *)
  | RefRelease of RefID.t                       (* Release a reference *)



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


(* Strip expression identifiers from the RefTracking output. *)
let rec drop_ids (id_expr : RefTracking.t) : t =
  match id_expr.RefTracking.expr with
  | RefTracking.Unit                             -> Unit
  | RefTracking.Int x                            -> Int x
  | RefTracking.BinaryOp (op, a, b)              -> BinaryOp (op, a, b)
  | RefTracking.UnaryOp (op, a)                  -> UnaryOp (op, a)
  | RefTracking.Conditional (cond, a, b, e1, e2) -> Conditional (cond, a, b, drop_ids e1, drop_ids e2)
  | RefTracking.Var v                            -> Var v
  | RefTracking.KnownFuncVar v                   -> KnownFuncVar v
  | RefTracking.Let (a, e1, e2)                  -> Let (a, drop_ids e1, drop_ids e2)
  | RefTracking.ApplyKnown (f, args)             -> ApplyKnown (f, args)
  | RefTracking.ApplyUnknown (f, args)           -> ApplyUnknown (f, args)
  | RefTracking.ArrayAlloc size                  -> ArrayAlloc size
  | RefTracking.ArrayInitOne (arr, index, v)     -> ArrayInitOne (arr, index, v)
  | RefTracking.ArraySet (arr, index, v)         -> ArraySet (arr, index, v)
  | RefTracking.ArrayGetVal (arr, index)         -> ArrayGetVal (arr, index)
  | RefTracking.ArrayGetRef (arr, index)         -> ArrayGetRef (arr, index)
  | RefTracking.RefClone r                       -> RefClone r
  | RefTracking.RefRelease r                     -> RefRelease r


(* Strip expression identifiers from the whole-program RefTracking output. *)
let drop_ids_program (program : RefTracking.program_t) : program_t =
  let functions =
    VMap.fold
      (fun f_id f_def acc ->
        let f_def' = {
          f_name = f_def.RefTracking.f_name;
          f_impl =
            match f_def.RefTracking.f_impl with
            | RefTracking.NativeFunc (args, body) ->
                NativeFunc (args, drop_ids body)
            | RefTracking.ExtFunc (name, arg_count) ->
                ExtFunc (name, arg_count)
        } in
        VMap.add f_id f_def' acc)
      program.RefTracking.functions
      VMap.empty
  in
  {functions; entry_point = program.RefTracking.entry_point}


