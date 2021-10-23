Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import ProofMode.

Set Implicit Arguments.



Instance multRA: URA.t := Excl.t Z%ra.

Section PROOF.

  Context `{@GRA.inG multRA Σ}.

  Definition f_spec: fspec := mk_simple (fun (_: unit) => ((fun varg o => (OwnM (Some 5%Z) ** ⌜o = ord_top⌝)%I),
                                                           (fun vret => (OwnM (Some 7%Z))%I))).
  Definition GlobalStb: gname -> option fspec := to_stb [("f", f_spec)].

End PROOF.
