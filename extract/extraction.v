Require Import ImpPrelude.
Require Import ModSem.
Require Import ClassicalDescription.

Require Coq.extraction.Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
(* Require Import Coq.extraction.ExtrOcamlZInt. *)
(* Require Import ExtrOcamlNatInt. *)

Extraction Blacklist List String Int.

Extract Constant excluded_middle_informative => "true".
Extract Constant assume => "(fun _ -> lazy (Coq_go (RetF ())))".
Extract Constant guarantee => "(fun _ -> lazy (Coq_go (RetF ())))".

Require Import MutFG Example0 EchoAll (* MWAll *) Imp ImpNotations.
        (* EchoAll *)

Cd "extract".

Separate Extraction Z.to_nat Z.opp mutsum_imp mutsum ex0 echo_impl_itr echo_spec_itr echo_imp_itr
         (* mw_impl_itr mw_abs_itr EXTRACT_MW_IMPL_LINKING_CHECK *)
.
         (* echo_prog *)

Cd "..".
