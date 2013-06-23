
type file_range_t = {
(** [file_range_t] is a representation of a range of characters in a source file. *)
  fr_start : Lexing.position;   (** Starting position of a range of characters *)
  fr_end   : Lexing.position;   (** Ending position of a range of characters *)
}

type parser_meta_t = {
  range      : file_range_t;                (** Location in file where expression is found *)
  type_annot : Type.type_scheme_t option;   (** Type annotation for this expression, if provided *)
}


