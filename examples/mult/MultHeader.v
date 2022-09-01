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
Instance gRA: URA.t := Excl.t nat%ra.
Instance hRA: URA.t := Excl.t bool%ra.
Definition fblack: fRA := ε.
Definition f0: fRA := Some 5%Z.
Definition f1: fRA := Some 6%Z.
Definition f2: fRA := Some 7%Z.
Definition f3: fRA := Some 8%Z.
Definition gpre (n: nat): gRA := Some n.
Definition gpost (n: nat): gRA := Some (n + 1).
Definition hpre: hRA := Some true.
Definition hpost: hRA := Some false.

Lemma f01_update: URA.updatable (fblack ⋅ f0) (fblack ⋅ f1).
Proof. eapply URA.updatable_add; try refl. eapply Excl.updatable; et. ur; ss. Qed.
Lemma f23_update: URA.updatable (fblack ⋅ f2) (fblack ⋅ f3).
Proof. eapply URA.updatable_add; try refl. eapply Excl.updatable; et. ur; ss. Qed.

Global Opaque f0 f1 f2 f3 gpre gpost hpre hpost.

Section PROOF.

  Context `{@GRA.inG fRA Σ}.
  Context `{@GRA.inG gRA Σ}.
  Context `{@GRA.inG hRA Σ}.

  Definition f_spec0: fspec :=
    mk_simple (fun (n: nat) => (ord_top,
                                  (fun _ => (OwnM f1 ** OwnM (gpre n))%I),
                                  (fun _ => (OwnM f2 ** OwnM (gpost n))%I))).
  Definition f_spec1: fspec :=
    mk_simple (fun (n: nat) => (ord_top,
                                  (fun _ => (OwnM f0 ** OwnM (gpre n) ** OwnM hpre)%I),
                                  (fun _ => (OwnM f3 ** OwnM (gpost n) ** OwnM hpost)%I))).
  Definition g_spec: fspec := mk_simple (fun (n: nat) => (ord_top,
                                                           (fun _ => (OwnM (gpre n))%I),
                                                           (fun _ => (OwnM (gpost n))%I))).
  Definition h_spec0: fspec := fspec_trivial.
  Definition h_spec1: fspec := mk_simple (fun (_: unit) => (ord_top,
                                                            (fun _ => (OwnM hpre)%I),
                                                            (fun _ => (OwnM hpost)%I))).

  Definition GlobalStb0: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("feasy", f_spec0); ("fhard", f_spec0); ("g", g_spec); ("h", h_spec0)].
  Defined.

  Definition GlobalStb1: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("feasy", f_spec0); ("fhard", f_spec1); ("g", g_spec); ("h", h_spec1)].
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

(*** TODO: move to PCM.v ***)
Lemma GRA_unit: ∀ {A : URA.t} {Σ : GRA.t} {H : GRA.inG A Σ}, GRA.embed (ε: A) = ε.
Proof.
 i. destruct H. subst. unfold GRA.embed.
 Local Transparent GRA.to_URA.
 unfold GRA.to_URA.
 cbn.
 Local Opaque GRA.to_URA.
 eapply func_ext_dep. i. des_ifs.
Qed.
