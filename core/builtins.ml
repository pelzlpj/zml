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

(* Built-in operators.  The parser recognizes operators and encodes them in the
 * AST using the associated built-in function names.  The names are in the
 * reserved namespace to prevent user code from rebinding them. *)

let leq       = "__zml_op_int_leq"
let geq       = "__zml_op_int_geq"
let less      = "__zml_op_int_less"
let greater   = "__zml_op_int_greater"
let add       = "__zml_op_int_add"
let sub       = "__zml_op_int_sub"
let mul       = "__zml_op_int_mul"
let div       = "__zml_op_int_div"
let modulus   = "__zml_op_int_mod"
let logic_not = "__zml_op_int_not"
let neg       = "__zml_op_int_neg"

(* These "pseudofunctions" don't actually have assembly implementations. They
 * are injected into the AST for the typing phase, but later compilation
 * passes rewrite the function names into the specialized variants which follow. *)
let eq          = "__zml_op_pseudofunc_poly_eq"
let neq         = "__zml_op_pseudofunc_poly_neq"
let array_get   = "__zml_pseudofunc_array_get"
let array_set   = "__zml_pseudofunc_array_set"
let array_alloc = "__zml_array_alloc"

(* Specialized variants of the pseudofunctions. *)
let array_get_val = "__zml_array_get_value"
let array_get_ref = "__zml_array_get_ref"
let array_set_val = "__zml_array_set_value"
let array_set_ref = "__zml_array_set_ref"

(* Low-level array management, never exposed to user code. *)
let array_alloc    = "__zml_array_alloc"
let array_init_one = "__zml_array_init_one"
let array_make     = "__zml_pseudofunc_array_make"

let ref_clone   = "__zml_ref_clone"
let ref_release = "__zml_ref_release"


module TVSet = Type.TVSet

(* Language-level built-in functions are all typed via the following environment definitions. *)
let type_env =
  let tv = TypeVar.fresh () in
  let ts_poly_comp =
    Type.ForAll (TVSet.singleton tv, Type.Arrow (Type.Var tv, Type.Arrow (Type.Var tv, Type.Bool))) in
  let ts_int_comp =
    Type.ForAll (TVSet.empty, Type.Arrow (Type.Int, Type.Arrow (Type.Int, Type.Bool))) in
  let ts_int_op =
    Type.ForAll (TVSet.empty, Type.Arrow (Type.Int, Type.Arrow (Type.Int, Type.Int))) in 
  [
    (* val (=) : 'a -> 'a -> bool *)
    (eq, ts_poly_comp);
    (* val (<>) : 'a -> 'a -> bool *)
    (neq, ts_poly_comp);
    (* val (<=) : int -> int -> bool *)
    (leq, ts_int_comp);
    (* val (>=) : int -> int -> bool *)
    (geq, ts_int_comp);
    (* val (<) : int -> int -> bool *)
    (less, ts_int_comp);
    (* val (>) : int -> int -> bool *)
    (greater, ts_int_comp);
    (* val (+) : int -> int -> int *)
    (add, ts_int_op);
    (* val (-) : int -> int -> int *)
    (sub, ts_int_op);
    (* val mult : int -> int -> int *)
    (mul, ts_int_op);
    (* val (/) : int -> int -> int *)
    (div, ts_int_op);
    (* val (mod) : int -> int -> int *)
    (modulus, ts_int_op);
    (* logical not; val not : bool -> bool *)
    (logic_not, Type.ForAll (TVSet.empty, Type.Arrow (Type.Bool, Type.Bool)));
    (* integer negation: val neg : int -> int *)
    (neg, Type.ForAll (TVSet.empty, Type.Arrow (Type.Int, Type.Int)));
    (* val array_get : 'a array -> int -> 'a *)
    (array_get,
      Type.ForAll (TVSet.singleton tv,
        Type.Arrow (Type.Array (Type.Var tv), Type.Arrow (Type.Int, Type.Var tv))));
    (* val array_set : 'a array -> int -> 'a -> unit *)
    (array_set,
      Type.ForAll (TVSet.singleton tv,
        Type.Arrow (Type.Array (Type.Var tv), Type.Arrow (Type.Int,
          Type.Arrow (Type.Var tv, Type.Unit)))));

    (* The following are not injected into the AST until after typing is complete, so
     * no guarantees about type soundness, etc.  The typing is only important for the
     * purpose of counting arguments. *)

    (* val array_alloc : int -> int array *)
    (array_alloc,
      Type.ForAll (TVSet.empty, Type.Arrow (Type.Int, Type.Array (Type.Int))));

    (* val array_init_one : int array -> int -> int -> int -> unit
     * (The final argument is a boolean "is_ref" flag.) *)
    (array_init_one,
      Type.ForAll (TVSet.empty,
        Type.Arrow (Type.Array Type.Int,
          Type.Arrow (Type.Int,
            Type.Arrow (Type.Int, 
              Type.Arrow (Type.Int, Type.Unit))))));

    (* val array_make : int -> int -> int array *)
    (array_make,
      Type.ForAll (TVSet.empty,
        Type.Arrow (Type.Int,
          Type.Arrow (Type.Int, Type.Array (Type.Int)))));

    (* val array_get_val : int array -> int -> int *)
    (array_get_val, Type.ForAll (TVSet.empty,
      Type.Arrow (Type.Array Type.Int, Type.Arrow (Type.Int, Type.Int))));

    (* val array_get_ref : int array -> int -> int *)
    (array_get_ref, Type.ForAll (TVSet.empty,
      Type.Arrow (Type.Array Type.Int, Type.Arrow (Type.Int, Type.Int))));

    (* val ref_clone : int -> int *)
    (ref_clone, Type.ForAll (TVSet.empty, Type.Arrow (Type.Int, Type.Int)));

    (* val ref_release : int -> unit *)
    (ref_release, Type.ForAll (TVSet.empty, Type.Arrow (Type.Int, Type.Unit)))

  ]


let asm_table =
	let asm_id_assoc = [
		(leq            , "zml_op_int_leq");
		(geq            , "zml_op_int_geq");
		(less           , "zml_op_int_less");
		(greater        , "zml_op_int_greater");
		(add            , "zml_op_int_add");
		(sub            , "zml_op_int_sub");
		(mul            , "zml_op_int_mul");
		(div            , "zml_op_int_div");
		(modulus        , "zml_op_int_mod)");
		(logic_not      , "zml_op_int_not");
		(neg            , "zml_op_int_neg");
		(array_get_val  , "zml_array_get_value");
		(array_get_ref  , "zml_array_get_ref");
		(array_set_val  , "zml_array_set_value");
		(array_set_ref  , "zml_array_set_ref");
		(array_alloc    , "zml_array_alloc");
		(array_init_one , "zml_array_init_one");
		(array_make     , "zml_array_create");
		(ref_clone      , "zml_ref_clone");
		(ref_release    , "zml_ref_release")
	] in
	let table = Hashtbl.create 50 in
	let () = List.iter (fun (id, asm_name) -> Hashtbl.add table id asm_name) asm_id_assoc in
	table


let asm_name_of_id (id : string) : string =
	try
		Hashtbl.find asm_table id
	with Not_found ->
		(* Make it obvious that this symbol should never appear in the asm *)
		id ^ "__UNDEFINED"

