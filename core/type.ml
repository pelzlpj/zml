
type t =
  | Unit
  | Int
  | Bool
  | Fun of (t list * t)

