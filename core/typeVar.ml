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

type t = int

let compare i j = if i < j then -1 else if i > j then 1 else 0

let typevar_count = ref 0

let reset_vars () =
  typevar_count := 0

let fresh () =
  let result = !typevar_count in
  let () = incr typevar_count in
  result

(* Represents type variables using the following pattern:
 * 'a, 'b, ..., 'z, 'a1, 'a2, ..., 'aN *)
let string_of tv =
  let num_chars = 26 in
  if tv < num_chars then
    Printf.sprintf "'%c" (Char.chr (tv + (Char.code 'a')))
  else
    Printf.sprintf "a%d" (tv + 1 - num_chars)

let of_int i = i

