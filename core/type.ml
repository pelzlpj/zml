 
type t =
  | Unit                   (** unit type *)
  | Bool                   (** boolean type *)
  | Int                    (** integer type *)
  | Var of string          (** a type variable *)
  | Arrow of t * t         (** an "arrow", i.e. type of a unary lambda *)


