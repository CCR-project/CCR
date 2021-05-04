Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import PCM.
Require Import Any.
Require Import ITreelib.

Set Implicit Arguments.
Set Typeclasses Depth 5.


Create HintDb iprop.
Ltac uipropall :=
  try (autounfold with iprop; autorewrite with iprop;
       all_once_fast ltac:(fun H => autounfold with iprop in H; autorewrite with iprop in H)).

Section IPROP.
  Context {Σ: GRA.t}.
  Definition iProp' := Σ -> Prop.

  Definition Sepconj (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => exists a b, r = URA.add a b /\ P a /\ Q b).
  Definition Pure (P: Prop): iProp' :=
    Seal.sealing
      "iProp"
      (fun _ => P).
  Definition Ex {X: Type} (P: X -> iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => exists x, P x r).
  Definition Univ {X: Type} (P: X -> iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => forall x, P x r).
  Definition Own (r0: Σ): iProp' :=
    Seal.sealing
      "iProp"
      (fun r1 => URA.extends r0 r1).
  Definition And (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => P r /\ Q r).
  Definition Or (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => P r \/ Q r).
  Definition Impl (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => URA.wf r -> P r -> Q r).
  Definition Wand (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => forall rp, URA.wf (r ⋅ rp) -> P rp -> Q (r ⋅ rp)).
  Definition Emp: iProp' :=
    Seal.sealing
      "iProp"
      (eq ε).
  Definition Persistently (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (Pure (P ε)).
  Definition Later (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      P.
  Definition Upd (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r0 => forall ctx, URA.wf (r0 ⋅ ctx) -> exists r1, URA.wf (r1 ⋅ ctx) /\ P r1).

  Definition Entails (P Q : iProp') : Prop :=
    Seal.sealing
      "iProp"
      (forall r (WF: URA.wf r), P r -> Q r).

  Hint Rewrite (Seal.sealing_eq "iProp"): iprop.
  #[local] Hint Unfold Sepconj Pure Ex Univ Own And Or Impl Wand Emp Persistently Later Upd Entails: iprop.

  (* BI axioms *)
  Global Program Instance PreOrder_Entails: PreOrder Entails.
  Next Obligation.
  Proof.
    ii. uipropall. ss.
  Qed.
  Next Obligation.
  Proof.
    ii. uipropall. ii. exploit (H r); et.
  Qed.

  Lemma Pure_intro: forall (φ : Prop) (P : iProp'), φ -> Entails P (Pure φ).
  Proof.
    ii. uipropall. ss.
  Qed.

  Lemma Pure_elim: forall (φ : Prop) (P : iProp'), (φ -> Entails (Pure True) P) -> Entails (Pure φ) P.
  Proof.
    ii. uipropall. ii. eapply H in H0; et.
  Qed.

  Lemma And_elim_l: forall P Q : iProp', Entails (And P Q) P.
  Proof.
    ii. uipropall. ii. eapply H.
  Qed.

  Lemma And_elim_r: forall P Q : iProp', Entails (And P Q) Q.
  Proof.
    ii. uipropall. ii. eapply H.
  Qed.

  Lemma And_intro: forall P Q R : iProp', Entails P Q -> Entails P R -> Entails P (And Q R).
  Proof.
    ii. uipropall. ii. split; [eapply H|eapply H0]; et.
  Qed.

  Lemma Or_intro_l: forall P Q : iProp', Entails P (Or P Q).
  Proof.
    ii. uipropall. ii. left. ss.
  Qed.

  Lemma Or_intro_r: forall P Q : iProp', Entails Q (Or P Q).
  Proof.
    ii. uipropall. ii. right. ss.
  Qed.

  Lemma Or_elim: forall P Q R : iProp', Entails P R -> Entails Q R -> Entails (Or P Q) R.
  Proof.
    ii. uipropall. ii. inv H1.
    { eapply H; ss. }
    { eapply H0; ss. }
  Qed.

  Lemma Impl_intro_r: forall P Q R : iProp', Entails (And P Q) R -> Entails P (Impl Q R).
  Proof.
    ii. uipropall. ii. eapply H; et.
  Qed.

  Lemma Impl_elim_l: forall P Q R : iProp', Entails P (Impl Q R) -> Entails (And P Q) R.
  Proof.
    ii. uipropall. ii. inv H0. eapply H; et.
  Qed.

  Lemma Univ_intro: forall (A : Type) (P : iProp') (Ψ : A -> iProp'), (forall a : A, Entails P (Ψ a)) -> Entails P (Univ (fun a : A => Ψ a)).
  Proof.
    ii. uipropall. ii. specialize (H x). uipropall. eapply H; et.
  Qed.

  Lemma Univ_elim: forall (A : Type) (Ψ : A -> iProp') (a : A), Entails (Univ (fun a0 : A => Ψ a0)) (Ψ a).
  Proof.
    ii. uipropall. ii. eapply H; et.
  Qed.

  Lemma Ex_intro: forall (A : Type) (Ψ : A -> iProp') (a : A), Entails (Ψ a) (Ex (fun a0 : A => Ψ a0)).
  Proof.
    ii. uipropall. ii. eexists. eauto.
  Qed.

  Lemma Ex_elim: forall (A : Type) (Φ : A -> iProp') (Q : iProp'), (forall a : A, Entails (Φ a) Q) -> Entails (Ex (fun a : A => Φ a)) Q.
  Proof.
    ii. uipropall. ii. des. specialize (H x). uipropall. et.
  Qed.

  Lemma Sepconj_mono: forall P P' Q Q' : iProp', Entails P Q -> Entails P' Q' -> Entails (Sepconj P P') (Sepconj Q Q').
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des; subst. esplits; et.
    { eapply H; et. eapply URA.wf_mon; et. }
    { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
  Qed.

  Lemma Emp_Sepconj_l: forall P : iProp', Entails P (Sepconj Emp P).
  Proof.
    ii. uipropall. ii. exists ε, r. splits; ss. rewrite URA.unit_idl. et.
  Qed.

  Lemma Emp_Sepconj_r: forall P : iProp', Entails (Sepconj Emp P) P.
  Proof.
    ii. uipropall. ii. inv H. des; subst. rewrite URA.unit_idl. et.
  Qed.

  Lemma Sepconj_comm: forall P Q : iProp', Entails (Sepconj P Q) (Sepconj Q P).
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des. subst. exists b, a. splits; et. apply URA.add_comm.
  Qed.

  Lemma Sepconj_assoc: forall P Q R : iProp', Entails (Sepconj (Sepconj P Q) R) (Sepconj P (Sepconj Q R)).
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des; subst. esplits; [|apply H2| |apply H3|apply H1]; ss.
    rewrite URA.add_assoc. ss.
  Qed.

  Lemma Wand_intro_r: forall P Q R : iProp', Entails (Sepconj P Q) R -> Entails P (Wand Q R).
  Proof.
    ii. uipropall. ii. eapply H; et.
  Qed.

  Lemma Wand_elim_l: forall P Q R : iProp', Entails P (Wand Q R) -> Entails (Sepconj P Q) R.
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des; subst. eapply H; et. eapply URA.wf_mon; et.
  Qed.

  Lemma Upd_intro: forall P : iProp', Entails P (Upd P).
  Proof.
    ii. uipropall. ii. exists r. splits; auto.
  Qed.

  Lemma Upd_mono: forall P Q : iProp', Entails P Q -> Entails (Upd P) (Upd Q).
  Proof.
    ii. uipropall. ii. exploit H0; et. i. des.
    exploit (H r1); et. eapply URA.wf_mon; et.
  Qed.

  Lemma Upd_trans: forall P : iProp', Entails (Upd (Upd P)) (Upd P).
  Proof.
    ii. uipropall. ii. exploit H; et. i. des. exploit x0; eauto.
  Qed.

  Lemma Upd_frame_r: forall P R : iProp', Entails (Sepconj (Upd P) R) (Upd (Sepconj P R)).
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des. subst. exploit (H1 (b ⋅ ctx)); et.
    { rewrite URA.add_assoc. et. }
    i. des. esplits; [..|eapply x1|eapply H2]; ss.
    rewrite <- URA.add_assoc. et.
  Qed.
End IPROP.
Hint Rewrite (Seal.sealing_eq "iProp"): iprop.
#[export] Hint Unfold Sepconj Pure Ex Univ Own And Or Impl Wand Emp Persistently Later Upd Entails: iprop.


From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.

Section IPM.
  Context {Σ: GRA.t}.

  (* Trivial Ofe Structure *)
  Inductive uPred_equiv' (P Q : iProp') : Prop :=
    { uPred_in_equiv : ∀ x, URA.wf x -> P x <-> Q x }.

  Local Instance uPred_equiv : Equiv iProp' := uPred_equiv'.
  Definition uPred_dist' (n : nat) (P Q : iProp') : Prop := uPred_equiv' P Q.
  Local Instance uPred_dist : Dist iProp' := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin iProp'.
  Proof.
    split.
    - intros P Q; split.
      + ii. ss.
      + ii. specialize (H 0). ss.
    - i. split.
      + ii. ss.
      + ii. econs. i. symmetry. apply H. auto.
      + ii. econs. i. transitivity (y x0); [apply H|apply H0]; ss.
    - i. ss.
  Qed.
  Canonical Structure uPredO : ofe := Ofe iProp' uPred_ofe_mixin.

  Program Definition uPred_compl : Compl uPredO := λ c x, forall n, c n x.

  Global Program Instance uPred_cofe : Cofe uPredO := {| compl := uPred_compl |}.
  Next Obligation.
    econs. i. split.
    - ii. exploit H0; et.
    - ii. destruct (le_ge_dec n n0).
      + apply c in l. apply l in H0; et.
      + apply c in g. apply g in H0; et.
  Qed.

  Lemma iProp_bi_mixin:
    BiMixin
      Entails Emp Pure And Or Impl
      (@Univ _) (@Ex _) Sepconj Wand
      Persistently.
  Proof.
    econs.
    - exact PreOrder_Entails.
    - econs.
      { uipropall. ii. split; ii; eapply H; et. }
      { uipropall. i. econs. i. des. split; i.
        { eapply H; et. }
        { eapply H1; et. }
      }
    - econs. i. split.
      { uipropall. ii. eapply H. ss. }
      { uipropall. ii. eapply H. ss. }
    - econs. i. split.
      { uipropall. ii. inv H2. split.
        { eapply H; et. }
        { eapply H0; et. }
      }
      { uipropall. ii. inv H2. split.
        { eapply H; et. }
        { eapply H0; et. }
      }
    - econs. i. split.
      { uipropall. ii. inv H2.
        { left. eapply H; et. }
        { right. eapply H0; et. }
      }
      { uipropall. ii. inv H2.
        { left. eapply H; et. }
        { right. eapply H0; et. }
      }
    - econs. i. split.
      { uipropall. ii. eapply H0; et. eapply H2; et. eapply H; et. }
      { uipropall. ii. eapply H0; et. eapply H2; et. eapply H; et. }
    - econs. i. split.
      { uipropall. ii. exploit H; et. i. eapply x2; et. }
      { uipropall. ii. exploit H; et. i. eapply x2; et. }
    - econs. i. split.
      { uipropall. ii. inv H1. exploit H; et. i. eexists. eapply x2; et. }
      { uipropall. ii. inv H1. exploit H; et. i. eexists. eapply x2; et. }
    - econs. i. split.
      { uipropall. ii. inv H2. des. subst. eexists. esplits; eauto.
        { eapply H; et. eapply URA.wf_mon; et. }
        { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
      }
      { uipropall. ii. inv H2. des. subst. eexists. esplits; eauto.
        { eapply H; et. eapply URA.wf_mon; et. }
        { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
      }
    - econs. uipropall. i. split.
      { ii. exploit H2; et.
        { eapply H; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
        { i. eapply H0; et. }
      }
      { ii. exploit H2; et.
        { eapply H; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
        { i. eapply H0; et. }
      }
    - ii. econs. uipropall. i. split.
      { ii. eapply H; ss. eapply URA.wf_unit. }
      { ii. eapply H; ss. eapply URA.wf_unit. }
    - exact Pure_intro.
    - exact Pure_elim.
    - exact And_elim_l.
    - exact And_elim_r.
    - exact And_intro.
    - exact Or_intro_l.
    - exact Or_intro_r.
    - exact Or_elim.
    - exact Impl_intro_r.
    - exact Impl_elim_l.
    - exact Univ_intro.
    - exact Univ_elim.
    - exact Ex_intro.
    - exact Ex_elim.
    - exact Sepconj_mono.
    - exact Emp_Sepconj_l.
    - exact Emp_Sepconj_r.
    - exact Sepconj_comm.
    - exact Sepconj_assoc.
    - exact Wand_intro_r.
    - exact Wand_elim_l.
    - ii. uipropall. i. eapply H; et. eapply URA.wf_unit.
    - ii. uipropall. i. eapply H; et.
    - ii. uipropall. ii. subst. ss.
    - ii. uipropall. ii. specialize (H x). uipropall. eapply H; et.
    - ii. uipropall. i. des. eexists. uipropall. et.
    - ii. uipropall. i. des. subst. ss.
    - ii. uipropall. ii. inv H. esplits; et. rewrite URA.unit_idl. et.
  Qed.

  Lemma iProp_bi_later_mixin:
    BiLaterMixin
      Entails Pure Or Impl
      (@Univ _) (@Ex _) Sepconj Persistently Later.
  Proof.
    econs.
    - ii. uipropall. i. split.
      { i. eapply H; et. }
    - ii. uipropall. eapply H; et.
    - ii. uipropall. ss.
    - ii. uipropall. ii. specialize (H x). uipropall. eapply H.
    - ii. uipropall. ii. right. des. exists x. uipropall. ss.
    - ii. uipropall. ss.
    - ii. uipropall. ss.
    - ii. uipropall. ss.
    - ii. uipropall. ss.
    - ii. uipropall. ii. right. ss.
  Qed.

  Canonical Structure iProp: bi :=
    {| bi_bi_mixin := iProp_bi_mixin;
       bi_bi_later_mixin := iProp_bi_later_mixin |}.

  (** extra BI instances *)
  Lemma iProp_bupd_mixin: BiBUpdMixin iProp Upd.
  Proof.
    econs.
    - ii. econs. unfold bupd. uipropall. i. split.
      { ii. exploit H1; eauto. i. des. esplits; eauto.
        eapply H; et. eapply URA.wf_mon; et. }
      { ii. exploit H1; eauto. i. des. esplits; eauto.
        eapply H; et. eapply URA.wf_mon; et. }
    - exact Upd_intro.
    - exact Upd_mono.
    - exact Upd_trans.
    - exact Upd_frame_r.
  Qed.
  Global Instance iProp_bi_bupd: BiBUpd iProp := {| bi_bupd_mixin := iProp_bupd_mixin |}.

  Global Instance iProp_bupd_absorbing (P: iProp): Absorbing (bupd P).
  Proof.
    ii. repeat red. unfold bupd, bi_bupd_bupd in *. ss. uipropall.
    ii. repeat red in H. uipropall. des. subst. exploit H2; et.
    eapply URA.wf_mon. rewrite URA.add_comm. rewrite URA.add_assoc. et.
  Qed.

  Global Instance iProp_pure_forall: BiPureForall iProp.
  Proof.
    ii. red. red. uipropall. ii. red. red in H.
    uipropall. i. specialize (H a). red in H. uipropall. ss.
  Qed.
End IPM.

Section TEST.
  Context {Σ: GRA.t}.

  Goal forall (P Q R: iProp) (PQ: P -∗ Q) (QR: Q -∗ R), P -∗ R.
  Proof.
    i. iStartProof. iIntros "H".
    iApply QR. iApply PQ. iApply "H".
  Qed.

  Goal forall (P Q: iProp), ((bupd P) ∗ Q) -∗ (bupd Q).
  Proof.
    i. iStartProof.
    iIntros "[Hxs Hys]". iMod "Hxs". iApply "Hys".
  Qed.
End TEST.
