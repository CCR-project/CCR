open BinNums
open BinPosDef
open Datatypes
open Nat

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred : positive -> positive

  val pred_N : positive -> coq_N

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val square : positive -> positive

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val size : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val max : positive -> positive -> positive

  val eqb : positive -> positive -> bool

  val leb : positive -> positive -> bool

  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive * mask) ->
    positive * mask

  val sqrtrem : positive -> positive * mask

  val coq_Nsucc_double : coq_N -> coq_N

  val coq_Ndouble : coq_N -> coq_N

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> coq_N

  val ldiff : positive -> positive -> coq_N

  val coq_lxor : positive -> positive -> coq_N

  val shiftl_nat : positive -> nat -> positive

  val shiftr_nat : positive -> nat -> positive

  val testbit : positive -> coq_N -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive

  val eq_dec : positive -> positive -> bool
 end
