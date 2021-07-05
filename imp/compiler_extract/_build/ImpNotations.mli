open BinNums
open Imp

module ImpNotations :
 sig
  val coq_Var_coerce : char list -> expr

  val coq_Lit_coerce : coq_Z -> expr
 end
