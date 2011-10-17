
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


type rename_context_t = {
  last_tvar : tvar_t;
  mapping   : tvar_t TVMap.t;
}

let empty_rename_ctx = {
  last_tvar = -1;
  mapping   = TVMap.empty
}


let remap_typevar (ctx : rename_context_t) (tvar : tvar_t) =
  try
    (ctx, TVMap.find tvar ctx.mapping)
  with Not_found ->
    let last_tvar = ctx.last_tvar + 1 in
    let mapping = TVMap.add tvar last_tvar ctx.mapping in
    ({last_tvar; mapping}, last_tvar)


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


