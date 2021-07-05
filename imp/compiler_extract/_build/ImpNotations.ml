open BinNums
open Imp

module ImpNotations =
 struct
  (** val coq_Var_coerce : char list -> expr **)

  let coq_Var_coerce x =
    Var x

  (** val coq_Lit_coerce : coq_Z -> expr **)

  let coq_Lit_coerce x =
    Lit x
 end
