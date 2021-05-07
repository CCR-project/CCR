Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import PCM.
Require Import Any.
Require Import ITreelib.
Require Import AList.

Set Implicit Arguments.
Set Typeclasses Depth 5.


Create HintDb iprop.
Ltac uipropall :=
  repeat (autounfold with iprop; autorewrite with iprop;
       all_once_fast ltac:(fun H => autounfold with iprop in H; autorewrite with iprop in H); ss).

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
  Definition OwnM (M: URA.t) `{@GRA.inG M Σ} (r: M): iProp' :=
    Own (GRA.embed r).
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
    ii. uipropall.
  Qed.
  Next Obligation.
  Proof.
    ii. uipropall. ii. exploit (H r); et.
  Qed.

  Lemma Pure_intro: forall (φ : Prop) (P : iProp'), φ -> Entails P (Pure φ).
  Proof.
    ii. uipropall.
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
    ii. uipropall.
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
Arguments OwnM: simpl never.


From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
Require Export UnableSsreflect.

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
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall. ii. specialize (H x). uipropall.
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
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall. ii. specialize (H x). uipropall.
    - ii. uipropall. ii. right. des. exists x. uipropall.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall.
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

  Global Instance iProp_own_absorbing r: Absorbing (Own r).
  Proof.
    ii. repeat red. uipropall. i. repeat red in H. uipropall.
    des. subst. etrans; eauto. exists a. apply URA.add_comm.
  Qed.

  Global Instance iProp_ownm_absorbing M `{@GRA.inG M Σ} (m: M): Absorbing (OwnM m).
  Proof.
    unfold OwnM. eapply iProp_own_absorbing.
  Qed.

  Global Instance iProp_pure_forall: BiPureForall iProp.
  Proof.
    ii. red. red. uipropall. ii. red. red in H.
    uipropall. i. specialize (H a). red in H. uipropall.
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

Infix "⊢" := (@bi_entails iProp).
Infix "**" := bi_sep (at level 99).
Infix "-*" := bi_wand (at level 99, right associativity).
Notation "#=> P" := ((@bupd (bi_car (@iProp _)) (@bi_bupd_bupd (@iProp _) (@iProp_bi_bupd _))) P) (at level 99).

Class IsOp {A : URA.t} (a b1 b2 : A) := is_op : a = URA.add b1 b2.
Global Arguments is_op {_} _ _ _ {_}.
Global Hint Mode IsOp + - - - : typeclass_instances.

Global Instance is_op_op {A : URA.t} (a b : A) : IsOp (URA.add a b) a b | 100.
Proof. by rewrite /IsOp. Qed.

Class IsOp' {A : URA.t} (a b1 b2 : A) := is_op' :> IsOp a b1 b2.
Global Hint Mode IsOp' + ! - - : typeclass_instances.
Global Hint Mode IsOp' + - ! ! : typeclass_instances.

Class IsOp'LR {A : URA.t} (a b1 b2 : A) := is_op_lr : IsOp a b1 b2.
Existing Instance is_op_lr | 0.
Global Hint Mode IsOp'LR + ! - - : typeclass_instances.
Global Instance is_op_lr_op {A : URA.t} (a b : A) : IsOp'LR (URA.add a b) a b | 0.
Proof. by rewrite /IsOp'LR /IsOp. Qed.

#[export] Hint Unfold bi_entails bi_sep bi_and bi_or bi_wand bupd bi_bupd_bupd: iprop.

Section class_instances.
  Context `{Σ: GRA.t}.

  Lemma from_semantic (a: Σ) (P: iProp') (SAT: P a)
    :
      Own a ⊢ #=> P.
  Proof.
    uipropall. ss. i. unfold URA.extends in *. des. subst.
    uipropall. i. esplits; [|apply SAT]. eapply URA.wf_mon.
    instantiate (1:=ctx0). replace (a ⋅ ctx ⋅ ctx0) with (a ⋅ ctx0 ⋅ ctx); et.
    repeat rewrite <- URA.add_assoc. f_equal. eapply URA.add_comm.
  Qed.

  Lemma to_semantic (a: Σ) (P: iProp') (SAT: Own a ⊢ P) (WF: URA.wf a)
    :
      P a.
  Proof.
    uipropall. eapply SAT; et. refl.
  Qed.

  Global Instance from_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 →
    FromSep (Own a) (Own b1) (Own b2).
  Proof.
    ii. inv H. red. uipropall. i. des. subst.
    unfold URA.extends in *. des. subst.
    exists (URA.add ctx0 ctx). repeat rewrite URA.add_assoc.
    f_equal. rewrite URA.add_comm. rewrite URA.add_assoc. f_equal.
    eapply URA.add_comm.
  Qed.

  Global Instance into_and_own p (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoAnd p (Own a) (Own b1) (Own b2).
  Proof.
    ii. apply bi.intuitionistically_if_mono. inv H.
    uipropall. i. unfold URA.extends in *. des. subst. split.
    { exists (URA.add b2 ctx). eapply URA.add_assoc. }
    { exists (URA.add b1 ctx). rewrite URA.add_assoc.
      f_equal. eapply URA.add_comm. }
  Qed.

  Global Instance into_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoSep (Own a) (Own b1) (Own b2).
  Proof.
    ii. red. inv H. uipropall. i.
    unfold URA.extends in *. des. subst.
    exists b1, (URA.add b2 ctx). split.
    { symmetry. eapply URA.add_assoc. }
    esplits.
    { eapply URA.unit_id. }
    { et. }
  Qed.

  Global Instance from_sep_ownM (M: URA.t) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 →
    FromSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. unfold OwnM. inv H0.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    rewrite GRA.embed_add. iApply "H".
  Qed.

  Global Instance into_and_ownM (M: URA.t) `{@GRA.inG M Σ} p (a b1 b2 : M) :
    IsOp a b1 b2 → IntoAnd p (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. apply bi.intuitionistically_if_mono. inv H0.
    unfold OwnM. rewrite <- GRA.embed_add. iIntros "[H1 H2]". iSplit.
    { iApply "H1". }
    { iApply "H2". }
  Qed.

  Global Instance into_sep_ownM (M: URA.t) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 → IntoSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. inv H0. unfold OwnM.
    rewrite <- GRA.embed_add. iIntros "[H1 H2]". iSplitL "H1"; iFrame.
  Qed.
End class_instances.



Section ILEMMAS.
  Context `{Σ: GRA.t}.

  Lemma Upd_Pure P
    :
      #=> ⌜P⌝ ⊢ ⌜P⌝.
  Proof.
    red. uipropall. i.
    hexploit (H URA.unit).
    { rewrite URA.unit_id. et. }
    i. des. red in H1. red. uipropall.
  Qed.

  Lemma Own_Upd_set
        (r1: Σ) B
        (UPD: URA.updatable_set r1 B)
    :
      (Own r1) ⊢ (#=> (∃ b, ⌜B b⌝ ** (Own b)))
  .
  Proof.
    cut (Entails (Own r1) (Upd (Ex (fun b => Sepconj (Pure (B b)) (Own b))))); ss.
    uipropall. i. red in H. des. subst.
    exploit (UPD (ctx0 ⋅ ctx)).
    { rewrite URA.add_assoc. et. }
    i. des. exists (b ⋅ ctx0). split.
    { rewrite <- URA.add_assoc. et. }
    { exists b. uipropall. esplits; [|apply IN|refl].
      eapply URA.add_comm. }
  Qed.

  Lemma Own_Upd
        (r1 r2: Σ)
        (UPD: URA.updatable r1 r2)
    :
      (Own r1) ⊢ (#=> (Own r2))
  .
  Proof.
    iStartProof. iIntros "H".
    iAssert (bupd (∃ b, bi_pure ((eq r2) b) ** (Own b)))%I with "[H]" as "H".
    { iApply Own_Upd_set; [|iFrame].
      red. red in UPD. i. hexploit UPD; et. }
    iMod "H". iDestruct "H" as (b) "[#H0 H1]".
    iPure "H0" as Hs. subst. iApply "H1".
  Qed.

  Lemma Own_extends
        (a b: Σ)
        (EXT: URA.extends a b)
    :
      Own b ⊢ Own a
  .
  Proof.
    red. uipropall. ii. etrans; et.
  Qed.

  Lemma OwnM_Upd_set (M: URA.t) `{@GRA.inG M Σ}
        (r1: M) B
        (UPD: URA.updatable_set r1 B)
    :
      (OwnM r1) ⊢ (#=> (∃ b, ⌜B b⌝ ** (OwnM b)))
  .
  Proof.
    admit "ez".
  Qed.

  Lemma OwnM_Upd (M: URA.t) `{@GRA.inG M Σ}
        (r1 r2: M)
        (UPD: URA.updatable r1 r2)
    :
      (OwnM r1) ⊢ (#=> (OwnM r2))
  .
  Proof.
    admit "ez".
  Qed.

  Lemma OwnM_extends (M: URA.t) `{@GRA.inG M Σ}
        (a b: M)
        (EXT: URA.extends a b)
    :
      OwnM b ⊢ OwnM a
  .
  Proof.
    admit "ez".
  Qed.

End ILEMMAS.


Section ILIST.
  Context `{Σ: GRA.t}.

  Definition iPropL := alist string iProp.

  (* Definition from_iPropL (l: iPropL): iProp := *)
  (*   fold_alist (fun _ P acc => P ** acc) (emp)%I l. *)

  Fixpoint from_iPropL (l: iPropL): iProp :=
    match l with
    | [] => (emp)%I
    | (_, Phd)::Ptl => Phd ** (from_iPropL Ptl)
    end.

  Definition from_iPropL2 (l: iPropL): iProp :=
    match l with
    | [(_, P)] => P
    | _ => from_iPropL l
    end.

  Lemma from_iPropL2_equiv l:
    from_iPropL l ⊢ from_iPropL2 l.
  Proof.
    destruct l; ss. destruct p. destruct l; ss.
    iIntros "[H _]". iApply "H".
  Qed.

  Lemma from_iPropL2_equiv2 l:
    from_iPropL2 l ⊢ from_iPropL l.
  Proof.
    destruct l; ss. destruct p. destruct l; ss.
    iIntros "H". iSplitL "H"; auto.
  Qed.

  Lemma iPropL_clear (Hn: string) (l: iPropL)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_remove Hn l).
  Proof.
    induction l; ss.
    { iIntros "H". iModIntro. iApply "H". }
    destruct a. des_ifs; ss.
    { iIntros "[H0 H1]". iSplitL "H0"; auto.
      iApply IHl. auto. }
    { iIntros "[_ H1]".
      iApply IHl. auto. }
  Qed.

  Lemma iPropL_one Hn (l: iPropL) (P: iProp)
        (FIND: alist_find Hn l = Some P)
    :
      from_iPropL l -∗ #=> P.
  Proof.

  Admitted.

  Lemma iPropL_entail Hn (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn l = Some P0)
        (ENTAIL: P0 -∗ P1)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn P1 l).
  Proof.
  Admitted.

  Lemma iPropL_destruct_ex Hn (l: iPropL) A (P: A -> iProp)
        (FIND: alist_find Hn l = Some (∃ (a: A), P a)%I)
    :
      from_iPropL l -∗ ∃ (a: A), #=> from_iPropL (alist_add Hn (P a) l).
  Proof.
  Admitted.

  Lemma iPropL_destruct_or Hn (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn l = Some (P0 ∨ P1)%I)
    :
      from_iPropL l -∗ (#=> from_iPropL (alist_add Hn P0 l)) ∨ #=> from_iPropL (alist_add Hn P1 l).
  Proof.
  Admitted.

  Lemma iPropL_destruct_sep Hn_old Hn_new0 Hn_new1 (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn_old l = Some (P0 ** P1))
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn_new1 P1 (alist_add Hn_new0 P0 (alist_remove Hn_old l))).
  Proof.
  Admitted.

  Lemma iPropL_upd Hn (l: iPropL) (P: iProp)
        (FIND: alist_find Hn l = Some (#=> P))
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn P l).
  Proof.
  Admitted.

  Lemma iPropL_assert (Hns: list string) (Hn_new: string) (l: iPropL) (P: iProp)
        (FIND: from_iPropL (fst (alist_pops Hns l)) -∗ P)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn_new P (snd (alist_pops Hns l))).
  Proof.
  Admitted.

  Lemma iPropL_init (Hn: string) (P: iProp)
    :
      P -∗ from_iPropL [(Hn, P)].
  Proof.
  Admitted.
End ILIST.
Arguments from_iPropL: simpl never.

Section CURRENT.
  Context `{Σ: GRA.t}.

  Variant current_iprops (ctx: Σ) (I: iProp): Prop :=
  | current_iprops_intro
      r
      (GWF: (@URA.wf (GRA.to_URA _) (URA.add r ctx)))
      (IPROP: I r)
  .

  Lemma current_iprops_entail I1 ctx I0
        (ACC: current_iprops ctx I0)
        (UPD: I0 ⊢ I1)
    :
      current_iprops ctx I1.
  Proof.
    inv ACC. econs; et.
    uipropall. eapply UPD; et. eapply URA.wf_mon; et.
  Qed.

  Lemma current_iprops_pure P ctx
        (ACC: current_iprops ctx (⌜P⌝)%I)
    :
      P.
  Proof.
    inv ACC. red in IPROP. uipropall.
  Qed.

  Lemma current_iprops_ex ctx A (P: A -> iProp)
        (ACC: current_iprops ctx (bi_exist P))
    :
      exists x, current_iprops ctx (P x).
  Proof.
    inv ACC. red in IPROP. uipropall.
    des. exists x. econs; et.
  Qed.

  Lemma current_iprops_or ctx I0 I1
        (ACC: current_iprops ctx (I0 ∨ I1)%I)
    :
      current_iprops ctx I0 \/ current_iprops ctx I1.
  Proof.
    inv ACC. uipropall. des.
    { left. econs; et. }
    { right. econs; et. }
  Qed.

  Lemma current_iprops_upd ctx I
        (ACC: current_iprops ctx (#=> I))
    :
      current_iprops ctx I.
  Proof.
    inv ACC. uipropall.
    hexploit IPROP; et. i. des. econs; et.
  Qed.

  Lemma current_iprops_own ctx (M: URA.t) `{@GRA.inG M Σ} (m: M)
        (ACC: current_iprops ctx (OwnM m))
    :
      URA.wf m.
  Proof.
    unfold OwnM in *.
    inv ACC. uipropall. unfold URA.extends in *. des. subst.
    eapply URA.wf_mon in GWF. eapply URA.wf_mon in GWF.
    eapply GRA.embed_wf. auto.
  Qed.
End CURRENT.



Section TACTICS.
  Context `{Σ: GRA.t}.

  Ltac on_current TAC :=
    match goal with
    | ACC: current_iprops _ (from_iPropL _) |- _ => TAC ACC
    end.

  Lemma current_iPropL_pure Hn ctx (l: iPropL) (P: Prop)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn l = Some (⌜P⌝)%I)
    :
      current_iprops ctx (from_iPropL (alist_remove Hn l)) /\ P.
  Proof.
    split.
    - eapply current_iprops_upd.
      eapply current_iprops_entail; et.
      eapply iPropL_clear.
    - eapply current_iprops_pure.
      eapply current_iprops_upd.
      eapply current_iprops_entail; et.
      eapply iPropL_one; et.
  Qed.

  Lemma current_iPropL_destruct_ex Hn ctx (l: iPropL) A (P: A -> iProp)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn l = Some (bi_exist P))
    :
      exists (a: A), current_iprops ctx (from_iPropL (alist_add Hn (P a) l)).
  Proof.
    eapply current_iprops_entail in ACC.
    2: { eapply iPropL_destruct_ex; et. }
    eapply current_iprops_ex in ACC. des.
    exists x. eapply current_iprops_upd. et.
  Qed.

  Lemma current_iPropL_destruct_or Hn ctx (l: iPropL) (P0 P1: iProp)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn l = Some (P0 ∨ P1)%I)
    :
      current_iprops ctx (from_iPropL (alist_add Hn P0 l)) \/
      current_iprops ctx (from_iPropL (alist_add Hn P1 l)).
  Proof.
    eapply current_iprops_entail in ACC.
    2: { eapply iPropL_destruct_or; et. }
    eapply current_iprops_or in ACC. des.
    { left. eapply current_iprops_upd. et. }
    { right. eapply current_iprops_upd. et. }
  Qed.

  Lemma current_iPropL_destruct_sep Hn_old Hn_new0 Hn_new1 ctx (l: iPropL) (P0 P1: iProp)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn_old l = Some (P0 ** P1)%I)
    :
      current_iprops ctx (from_iPropL (alist_add Hn_new1 P1 (alist_add Hn_new0 P0 (alist_remove Hn_old l)))).
  Proof.
    eapply current_iprops_upd.
    eapply current_iprops_entail; et.
    eapply iPropL_destruct_sep; et.
  Qed.

  Lemma current_iPropL_upd Hn ctx (l: iPropL) (P: iProp)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn l = Some (#=> P)%I)
    :
      current_iprops ctx (from_iPropL (alist_add Hn P l)).
  Proof.
    eapply current_iprops_upd.
    eapply current_iprops_entail; et.
    eapply iPropL_upd; et.
  Qed.

  Lemma current_iPropL_own_wf Hn ctx (l: iPropL) M `{@GRA.inG M Σ} (m: M)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn l = Some (OwnM m))
    :
      URA.wf m.
  Proof.
    eapply current_iprops_own.
    eapply current_iprops_upd.
    eapply current_iprops_entail; et.
    eapply iPropL_one; et.
  Qed.

  Lemma current_iPropL_clear Hn ctx (l: iPropL)
        (ACC: current_iprops ctx (from_iPropL l))
    :
      current_iprops ctx (from_iPropL (alist_remove Hn l)).
  Proof.
    eapply current_iprops_upd.
    eapply current_iprops_entail; et.
    eapply iPropL_clear; et.
  Qed.

  Lemma current_iPropL_assert Hns Hn_new (P: iProp) ctx (l: iPropL)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: from_iPropL (fst (alist_pops Hns l)) -∗ P)
    :
      current_iprops ctx (from_iPropL (alist_add Hn_new P (snd (alist_pops Hns l)))).
  Proof.
    eapply current_iprops_upd.
    eapply current_iprops_entail; et.
    eapply iPropL_assert; et.
  Qed.

  Lemma current_iPropL_entail Hn ctx (l: iPropL) (P0 P1: iProp)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn l = Some P0)
        (ENTAIL: P0 -∗ P1)
    :
      current_iprops ctx (from_iPropL (alist_add Hn P1 l)).
  Proof.
    eapply current_iprops_upd.
    eapply current_iprops_entail; et.
    eapply iPropL_entail; et.
  Qed.

  Lemma current_iPropL_univ Hn A a ctx (l: iPropL) (P: A -> iProp)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn l = Some (bi_forall P))
    :
      current_iprops ctx (from_iPropL (alist_add Hn (P a) l)).
  Proof.
    eapply current_iPropL_entail; et.
    iIntros "H".
    (* TODO which IPM tactic? *)
    iApply bi.forall_elim. ss.
  Qed.

  Lemma current_iPropL_wand Hn0 Hn1 ctx (l l0 l1: iPropL)
        (P0 P1: iProp)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND0: alist_pop Hn0 l = Some ((P0 -∗ P1)%I, l0))
        (FIND1: alist_pop Hn1 l0 = Some (P0, l1))
    :
      current_iprops ctx (from_iPropL (alist_add Hn0 P1 l1)).
  Proof.
    exploit (@current_iPropL_assert [Hn1; Hn0] Hn0 P1); et.
    { ss. rewrite FIND0. rewrite FIND1. ss.
      iIntros "[H0 [H1 _]]". iApply "H1". iApply "H0". }
    ss. rewrite FIND0. rewrite FIND1. ss.
  Qed.

  Lemma current_iPropL_destruct_and_l Hn ctx (l: iPropL) (P0 P1: iProp)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn l = Some (P0 ∧ P1)%I)
    :
      current_iprops ctx (from_iPropL (alist_add Hn P0 l)).
  Proof.
    eapply current_iPropL_entail; et.
    iIntros "H". iDestruct "H" as "[H _]". iApply "H".
  Qed.

  Lemma current_iPropL_destruct_and_r Hn ctx (l: iPropL) (P0 P1: iProp)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn l = Some (P0 ∧ P1)%I)
    :
      current_iprops ctx (from_iPropL (alist_add Hn P1 l)).
  Proof.
    eapply current_iPropL_entail; et.
    iIntros "H". iDestruct "H" as "[_ H]". iApply "H".
  Qed.

  Lemma list_filter_idemp A f (l: list A):
    List.filter f (List.filter f l) = List.filter f l.
  Proof.
    induction l; ss. des_ifs. ss. des_ifs. f_equal; auto.
  Qed.

  Lemma current_iPropL_destruct_sep' Hn_old Hn_new0 Hn_new1 ctx (l: iPropL) (P0 P1 P2: iProp)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn_old l = Some P2)
        (ENTAIL: P2 -∗ (P0 ** P1)%I)
    :
      current_iprops ctx (from_iPropL (alist_add Hn_new1 P1 (alist_add Hn_new0 P0 (alist_remove Hn_old l)))).
  Proof.
    eapply current_iPropL_entail in ACC; et.
    eapply (@current_iPropL_destruct_sep Hn_old Hn_new0 Hn_new1 _ _ P0 P1) in ACC; et.
    { match goal with
      | [H: current_iprops _ (from_iPropL ?l0) |- current_iprops _ (from_iPropL ?l1)] => replace l1 with l0
      end; auto.
      f_equal. f_equal. clear. unfold alist_add, alist_remove. ss.
      rewrite eq_rel_dec_correct. des_ifs. eapply list_filter_idemp.
    }
    { unfold alist_add, alist_remove. ss.
      rewrite eq_rel_dec_correct. des_ifs. }
  Qed.

  Lemma current_iPropL_destruct_and_pure_l
        Hn_old Hn_new0 Hn_new1 ctx (l: iPropL) (P0: iProp) (P1: Prop)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn_old l = Some (P0 ∧ (⌜P1⌝))%I)
    :
      current_iprops ctx (from_iPropL (alist_add Hn_new1 (⌜P1⌝)%I (alist_add Hn_new0 P0 (alist_remove Hn_old l)))).
  Proof.
    eapply current_iPropL_destruct_sep'; et.
    iIntros "H". iDestruct "H" as "[H0 H1]". iFrame.
  Qed.

  Lemma current_iPropL_destruct_and_pure_r
        Hn_old Hn_new0 Hn_new1 ctx (l: iPropL) (P0: Prop) (P1: iProp)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn_old l = Some ((⌜P0⌝) ∧ P1)%I)
    :
      current_iprops ctx (from_iPropL (alist_add Hn_new1 P1 (alist_add Hn_new0 (⌜P0⌝)%I (alist_remove Hn_old l)))).
  Proof.
    eapply current_iPropL_destruct_sep'; et.
    iIntros "H". iDestruct "H" as "[H0 H1]". iFrame.
  Qed.

  Lemma current_iPropL_destruct_own Hn_old Hn_new0 Hn_new1
        ctx (l: iPropL) M `{@GRA.inG M Σ} (m0 m1: M)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND: alist_find Hn_old l = Some (OwnM (URA.add m0 m1)))
    :
      current_iprops ctx (from_iPropL (alist_add Hn_new1 (OwnM m1) (alist_add Hn_new0 (OwnM m0) (alist_remove Hn_old l)))).
  Proof.
    eapply current_iPropL_destruct_sep'; et.
    iIntros "[H0 H1]". iFrame.
  Qed.

  Lemma current_iPropL_merge_own Hn0 Hn1 ctx (l l0 l1: iPropL)
        M `{@GRA.inG M Σ} (m0 m1: M)
        (ACC: current_iprops ctx (from_iPropL l))
        (FIND0: alist_pop Hn0 l = Some (OwnM m0, l0))
        (FIND1: alist_pop Hn1 l0 = Some (OwnM m1, l1))
    :
      current_iprops ctx (from_iPropL (alist_add Hn0 (OwnM (URA.add m0 m1)) l1)).
  Proof.
    exploit (@current_iPropL_assert [Hn1; Hn0] Hn0 (OwnM (URA.add m0 m1))); et.
    { ss. rewrite FIND0. rewrite FIND1. ss.
      iIntros "[H0 [H1 _]]". iSplitL "H1"; iFrame. }
    ss. rewrite FIND0. rewrite FIND1. ss.
  Qed.
End TACTICS.


Module PARSE.
  Section PARSE.
    Context `{Σ: GRA.t}.

    Inductive iProp_tree: Type :=
    | iProp_tree_base (P: iProp)
    | iProp_tree_binop (op: iProp -> iProp -> iProp) (tr0 tr1: iProp_tree)
    | iProp_tree_unop (op: iProp -> iProp) (tr: iProp_tree)
    | iProp_tree_kop A (op: (A -> iProp) -> iProp) (k: A -> iProp_tree)
    .

    Fixpoint from_iProp_tree (tr: iProp_tree): iProp :=
      match tr with
      | iProp_tree_base P => P
      | iProp_tree_binop op P Q => op (from_iProp_tree P) (from_iProp_tree Q)
      | iProp_tree_unop op P => op (from_iProp_tree P)
      | @iProp_tree_kop A op k => op (fun a => from_iProp_tree (k a))
      end.

    Definition hole (A: Type): A. Admitted.

    Ltac parse_iProp_tree p :=
      match p with
      | ?op (?P0: iProp) (?P1: iProp) =>
        let tr0 := parse_iProp_tree P0 in
        let tr1 := parse_iProp_tree P1 in
        constr:(iProp_tree_binop op tr0 tr1)
      | ?op (?P: iProp) =>
        let tr := parse_iProp_tree P in
        constr:(iProp_tree_unop op tr)
      | ?op ?k =>
        match type of k with
        | ?A -> bi_car iProp =>
          let khole := (eval cbn beta in (k (@hole A))) in
          let tr := parse_iProp_tree khole in
          let fhole := (eval pattern (@hole A) in tr) in
          match fhole with
          | ?f (@hole A) => constr:(@iProp_tree_kop A op f)
          end
        end
      | ?P => constr:(iProp_tree_base P)
      end.

    Definition iProp_list := alist string iProp_tree.

    Definition from_iProp_list (l: iProp_list): iProp :=
      fold_alist (fun _ tr acc => from_iProp_tree tr ** acc) (emp)%I l.
  End PARSE.
End PARSE.
