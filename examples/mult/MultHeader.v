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



Instance fRA: URA.t := Excl.t Z%ra.
Instance gRA: URA.t := Excl.t bool%ra.
Instance hRA: URA.t := Excl.t nat%ra.
Definition fpre: fRA := Some 5%Z.
Definition fpost: fRA := Some 7%Z.
Definition gpre: gRA := Some true.
Definition gpost: gRA := Some false.
Definition hpre: hRA := Some 15.
Definition hpost: hRA := Some 17.

Section PROOF.

  Context `{@GRA.inG fRA Σ}.
  Context `{@GRA.inG gRA Σ}.
  Context `{@GRA.inG hRA Σ}.

  Definition f_spec0: fspec := mk_simple (fun (_: unit) => ((fun varg o => (OwnM fpre ** ⌜o = ord_top⌝)%I),
                                                           (fun vret => (OwnM fpost)%I))).
  Definition f_spec1: fspec := mk_simple (fun (_: unit) => ((fun varg o => (OwnM fpre ** OwnM gpre ** ⌜o = ord_top⌝)%I),
                                                           (fun vret => (OwnM fpost ** OwnM gpost)%I))).
  Definition g_spec: fspec := mk_simple (fun (_: unit) => ((fun varg o => (OwnM gpre ** ⌜o = ord_top⌝)%I),
                                                           (fun vret => (OwnM gpost)%I))).
  Definition h_spec0: fspec := fspec_trivial.
  Definition h_spec1: fspec := mk_simple (fun (_: unit) => ((fun varg o => (OwnM hpre ** ⌜o = ord_top⌝)%I),
                                                           (fun vret => (OwnM hpost)%I))).

  Definition GlobalStb0: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("ff", f_spec0); ("f", f_spec0); ("g", g_spec); ("h", h_spec0)].
  Defined.

  Definition GlobalStb1: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("ff", f_spec0); ("f", f_spec1); ("g", g_spec); ("h", h_spec1)].
  Defined.

  (* Definition GlobalStb0: gname -> option fspec := to_stb [("f", f_spec0); ("g", g_spec); ("h", h_spec0)]. *)
  (* Definition GlobalStb1: gname -> option fspec := to_stb [("f", f_spec1); ("g", g_spec); ("h", h_spec1)]. *)

  (***
(f) arg/ret only
(g) tgt call meaningful spec
(h) tgt call trivial spec

update
module resource
APC
   ***)
End PROOF.

Global Hint Unfold GlobalStb0: stb.
Global Hint Unfold GlobalStb1: stb.
