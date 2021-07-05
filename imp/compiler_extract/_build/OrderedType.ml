
type 'x coq_Compare =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t coq_Compare

  val eq_dec : t -> t -> bool
 end
