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

include Map.OrderedType

(** [reset_vars ()] resets the state of the type variable allocator. *)
val reset_vars : unit -> unit

(** [fresh ()] allocates a fresh type variable. *)
val fresh      : unit -> t

(** [string_of tp] generates a string representation of a type variable.  Naming
    follows the pattern 'a, 'b, ..., 'z, 'a1, 'a2, ..., 'aN . *)
val string_of : t -> string

(** [of_int i] generates a type variable corresponding to integer [i]. *)
val of_int : int -> t

