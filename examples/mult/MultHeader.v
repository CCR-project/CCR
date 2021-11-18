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
Definition f0: fRA := Some 5%Z.
Definition f1: fRA := Some 6%Z.
Definition f2: fRA := Some 7%Z.
Definition f3: fRA := Some 8%Z.
Definition gpre: gRA := Some true.
Definition gpost: gRA := Some false.
Definition hpre: hRA := Some 15.
Definition hpost: hRA := Some 17.

Lemma f01_update: URA.updatable f0 f1.
Proof. eapply Excl.updatable; et. ur; ss. Qed.
Lemma f23_update: URA.updatable f2 f3.
Proof. eapply Excl.updatable; et. ur; ss. Qed.

Global Opaque f0 f1 f2 f3 gpre gpost hpre hpost.

Section PROOF.

  Context `{@GRA.inG fRA Σ}.
  Context `{@GRA.inG gRA Σ}.
  Context `{@GRA.inG hRA Σ}.

  Definition f_spec0: fspec := mk_simple (fun (_: unit) => (ord_top,
                                                            (fun varg => (OwnM f1 ** OwnM gpre)%I),
                                                           (fun vret => (OwnM f2 ** OwnM gpost)%I))).
  Definition f_spec1: fspec := mk_simple (fun (_: unit) => (ord_top,
                                                            (fun varg => (OwnM f0 ** OwnM gpre ** OwnM hpre)%I),
                                                           (fun vret => (OwnM f3 ** OwnM gpost ** OwnM hpost)%I))).
  Definition g_spec: fspec := mk_simple (fun (_: unit) => (ord_top,
                                                           (fun varg => (OwnM gpre)%I),
                                                           (fun vret => (OwnM gpost)%I))).
  Definition h_spec0: fspec := fspec_trivial.
  Definition h_spec1: fspec := mk_simple (fun (_: unit) => (ord_top,
                                                            (fun varg => (OwnM hpre)%I),
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
