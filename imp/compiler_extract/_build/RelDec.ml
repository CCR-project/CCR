
type 't coq_RelDec =
  't -> 't -> bool
  (* singleton inductive, whose constructor was Build_RelDec *)

(** val rel_dec : 'a1 coq_RelDec -> 'a1 -> 'a1 -> bool **)

let rel_dec relDec =
  relDec
