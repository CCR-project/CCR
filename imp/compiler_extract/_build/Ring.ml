open Datatypes

(** val bool_eq : bool -> bool -> bool **)

let bool_eq b1 b2 =
  if b1 then b2 else negb b2
