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

module TVSet = Set.Make(TypeVar)
module TVMap = Map.Make(TypeVar)


type t =
  | Unit                   (** unit type *)
  | Bool                   (** boolean type *)
  | Int                    (** integer type *)
  | Var of TypeVar.t       (** a type variable *)
  | Arrow of t * t         (** an "arrow", i.e. type of a unary lambda *)
  | Array of t             (** an array containing an arbitrary type *)

type type_scheme_t = ForAll of TVSet.t * t


let rec string_of_type typ =
  match typ with
  | Unit         -> "()"
  | Bool         -> "bool"
  | Int          -> "int"
  | Var i        -> TypeVar.string_of i
  | Arrow ((Arrow _ as a), b) ->
      (* This case occurs in a higher-order function *)
      Printf.sprintf "(%s) -> %s" (string_of_type a) (string_of_type b)
  | Arrow (a, b) ->
      Printf.sprintf "%s -> %s" (string_of_type a) (string_of_type b)
  | Array a ->
      Printf.sprintf "%s array" (string_of_type a)


type rename_context_t = {
  last_tvar : int;
  mapping   : int TVMap.t;
}

let empty_rename_ctx = {
  last_tvar = -1;
  mapping   = TVMap.empty
}


let remap_typevar (ctx : rename_context_t) (tvar : TypeVar.t)
  : rename_context_t * TypeVar.t =
  try
    (ctx, TypeVar.of_int (TVMap.find tvar ctx.mapping))
  with Not_found ->
    let last_tvar = ctx.last_tvar + 1 in
    let mapping = TVMap.add tvar last_tvar ctx.mapping in
    ({last_tvar; mapping}, TypeVar.of_int last_tvar)


(* Given a type expression as input, rename the type variables so that they use
 * the first N variable names. *)
let rec local_rename_typevars (ctx : rename_context_t) (x : t) =
  match x with
  | Unit | Bool | Int ->
      (ctx, x)
  | Var a ->
      let (ctx, a) = remap_typevar ctx a in
      (ctx, Var a)
  | Arrow (a, b) ->
      let (ctx, a) = local_rename_typevars ctx a in
      let (ctx, b) = local_rename_typevars ctx b in
      (ctx, Arrow (a, b))
  | Array a ->
      let (ctx, a) = local_rename_typevars ctx a in
      (ctx, Array a)


