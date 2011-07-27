
type primitive_t =
  | Unit
  | Bool
  | Int
 
type t =
  | TLit of primitive_t     (** literal value *)
  | TVar of string          (** a type variable *)
  | TArrow of t * t         (** an "arrow", i.e. type of a unary lambda *)


