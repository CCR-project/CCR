open BinInt
open BinNums
open BinPos
open Datatypes
open DecidableClass

(** val coq_Decidable_not : coq_Decidable -> coq_Decidable **)

let coq_Decidable_not dP =
  negb (coq_Decidable_witness dP)

(** val coq_Decidable_and :
    coq_Decidable -> coq_Decidable -> coq_Decidable **)

let coq_Decidable_and dP dQ =
  (&&) (coq_Decidable_witness dP) (coq_Decidable_witness dQ)

(** val coq_Decidable_or : coq_Decidable -> coq_Decidable -> coq_Decidable **)

let coq_Decidable_or dP dQ =
  (||) (coq_Decidable_witness dP) (coq_Decidable_witness dQ)

(** val coq_Decidable_implies :
    coq_Decidable -> coq_Decidable -> coq_Decidable **)

let coq_Decidable_implies dP dQ =
  if coq_Decidable_witness dP then coq_Decidable_witness dQ else true

(** val coq_Decidable_eq_positive : positive -> positive -> coq_Decidable **)

let coq_Decidable_eq_positive =
  Pos.eqb

(** val coq_Decidable_eq_Z : coq_Z -> coq_Z -> coq_Decidable **)

let coq_Decidable_eq_Z =
  Z.eqb

(** val coq_Decidable_le_Z : coq_Z -> coq_Z -> coq_Decidable **)

let coq_Decidable_le_Z =
  Z.leb

(** val coq_Decidable_ge_Z : coq_Z -> coq_Z -> coq_Decidable **)

let coq_Decidable_ge_Z =
  Z.geb

(** val coq_Decidable_gt_Z : coq_Z -> coq_Z -> coq_Decidable **)

let coq_Decidable_gt_Z =
  Z.gtb

(** val coq_Decidable_divides : coq_Z -> coq_Z -> coq_Decidable **)

let coq_Decidable_divides x y =
  Z.eqb y (Z.mul (Z.div y x) x)
