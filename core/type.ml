 
type t =
  | Unit                   (** unit type *)
  | Bool                   (** boolean type *)
  | Int                    (** integer type *)
  | Var of string          (** a type variable *)
  | Arrow of t * t         (** an "arrow", i.e. type of a unary lambda *)


let rec string_of_type typ =
  match typ with
  | Unit         -> "()"
  | Bool         -> "bool"
  | Int          -> "int"
  | Var s        -> Printf.sprintf "'%s" s
  | Arrow (a, b) -> Printf.sprintf "%s -> %s" (string_of_type a) (string_of_type b)

