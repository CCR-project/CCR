open BinInt
open BinNums
open BinPos
open Datatypes
open DecidableClass

val coq_Decidable_not : coq_Decidable -> coq_Decidable

val coq_Decidable_and : coq_Decidable -> coq_Decidable -> coq_Decidable

val coq_Decidable_or : coq_Decidable -> coq_Decidable -> coq_Decidable

val coq_Decidable_implies : coq_Decidable -> coq_Decidable -> coq_Decidable

val coq_Decidable_eq_positive : positive -> positive -> coq_Decidable

val coq_Decidable_eq_Z : coq_Z -> coq_Z -> coq_Decidable

val coq_Decidable_le_Z : coq_Z -> coq_Z -> coq_Decidable

val coq_Decidable_ge_Z : coq_Z -> coq_Z -> coq_Decidable

val coq_Decidable_gt_Z : coq_Z -> coq_Z -> coq_Decidable

val coq_Decidable_divides : coq_Z -> coq_Z -> coq_Decidable
