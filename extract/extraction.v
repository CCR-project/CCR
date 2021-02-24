Require Import Universe.
Require Import ModSem.
Require Import ClassicalDescription.

Require Coq.extraction.Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
(* Require Import Coq.extraction.ExtrOcamlZInt. *)
(* Require Import ExtrOcamlNatInt. *)

Extraction Blacklist List String Int.

Extract Constant excluded_middle_informative => "true".

Require Import MutFG Example0.

Cd "extract".

Separate Extraction Z.to_nat Z.opp mutsum ex0.

Cd "..".
