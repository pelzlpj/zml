
type tvar_t = int

module TVar = struct
  type t = tvar_t
  let compare i j =
    if i < j then -1
    else if i = 0 then 0
    else 1
end

module TVMap = Map.Make(TVar)


type t =
  | Unit                   (** unit type *)
  | Bool                   (** boolean type *)
  | Int                    (** integer type *)
  | Var of tvar_t          (** a type variable *)
  | Arrow of t * t         (** an "arrow", i.e. type of a unary lambda *)


let typevar_count = ref 0

let reset_type_vars () =
  typevar_count := 0

let make_type_var () : t =
  let result = !typevar_count in
  let () = incr typevar_count in
  Var result


(* Represents type variables using the following pattern:
 * 'a, 'b, ..., 'z, 'a1, 'a2, ..., 'aN *)
let string_of_typevar_index (index : tvar_t) =
  let num_chars = 26 in
  if index < num_chars then
    Printf.sprintf "'%c" (Char.chr (index + (Char.code 'a')))
  else
    Printf.sprintf "a%d" (index + 1 - num_chars)


let rec string_of_type typ =
  match typ with
  | Unit         -> "()"
  | Bool         -> "bool"
  | Int          -> "int"
  | Var i        -> string_of_typevar_index i
  | Arrow (a, b) -> Printf.sprintf "%s -> %s" (string_of_type a) (string_of_type b)


let remap_typevar (last_tvar : tvar_t) (mapping : tvar_t TVMap.t) (tvar : tvar_t) =
  try
    (last_tvar, mapping, TVMap.find tvar mapping)
  with Not_found ->
    let new_tvar = last_tvar + 1 in
    let mapping = TVMap.add tvar new_tvar mapping in
    (new_tvar, mapping, new_tvar)


(* Given a type expression as input, rename the type variables so that they use
 * the first N variable names. *)
let rec local_rename_typevars_aux (last_tvar : tvar_t) (mapping : tvar_t TVMap.t) (x : t) =
  match x with
  | Unit | Bool | Int ->
      (last_tvar, mapping, x)
  | Var a ->
      let (last_tvar, mapping, a) = remap_typevar last_tvar mapping a in
      (last_tvar, mapping, Var a)
  | Arrow (a, b) ->
      let (last_tvar, mapping, a) = local_rename_typevars_aux last_tvar mapping a in
      let (last_tvar, mapping, b) = local_rename_typevars_aux last_tvar mapping b in
      (last_tvar, mapping, Arrow (a, b))

let local_rename_typevars (x : t) : t =
  let (_, _, x') = local_rename_typevars_aux (-1) TVMap.empty x in
  x'


