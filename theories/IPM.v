From iris.bi Require Import derived_connectives updates internal_eq plainly.
From iris.prelude Require Import options.

Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import PCM.
Require Import Any.
Require Import ITreelib.

Set Implicit Arguments.
Set Typeclasses Depth 5.



Section IRIS.
  Context {Σ: GRA.t}.
  Definition iProp := Σ -> Prop.

  Definition Sepconj (P Q: iProp): iProp :=
    fun r => exists a b, r = URA.add a b /\ P a /\ Q b
  .
  Definition Pure (P: Prop): iProp := fun _ => P.
  Definition Ex {X: Type} (P: X -> iProp): iProp := fun r => exists x, P x r.
  Definition Univ {X: Type} (P: X -> iProp): iProp := fun r => forall x, P x r.
  Definition Own (r0: Σ): iProp := fun r1 => URA.extends r0 r1.
  Definition And (P Q: iProp): iProp := fun r => P r /\ Q r.
  Definition Or (P Q: iProp): iProp := fun r => P r \/ Q r.
  Definition Impl (P Q: iProp): iProp := fun r => URA.wf r -> P r -> Q r.
  Definition Wand (P Q: iProp): iProp := fun r => forall rp, URA.wf (r ⋅ rp) -> P rp -> Q (r ⋅ rp).

  Definition Entails (P Q: iProp): Prop := forall r (WF: URA.wf r), P r -> Q r.
  Definition Impure (P: iProp): Prop := P ε.

  Definition Upd (P: iProp): iProp := fun r0 => forall ctx, URA.wf (r0 ⋅ ctx) -> exists r1, URA.wf (r1 ⋅ ctx) /\ P r1.

  Definition Emp: iProp := eq ε.
  Definition Persistently (P: iProp): iProp := fun _ => False.

  (* Trivial Ofe Structure *)
  Inductive uPred_equiv' (P Q : iProp) : Prop :=
    { uPred_in_equiv : ∀ x, URA.wf x -> P x <-> Q x }.

  Local Instance uPred_equiv : Equiv iProp := uPred_equiv'.
  Definition uPred_dist' (n : nat) (P Q : iProp) : Prop := uPred_equiv' P Q.
  Local Instance uPred_dist : Dist iProp := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin iProp.
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
  Canonical Structure uPredO : ofe := Ofe iProp uPred_ofe_mixin.

  Program Definition uPred_compl : Compl uPredO := λ c x, forall n, c n x.

  Global Program Instance uPred_cofe : Cofe uPredO := {| compl := uPred_compl |}.
  Next Obligation.
    econs. i. split.
    - ii. exploit H0; et.
    - ii. destruct (le_ge_dec n n0).
      + apply c in l. apply l in H0; et.
      + apply c in g. apply g in H0; et.
  Qed.


  (* BI axioms *)

  Global Program Instance PreOrder_Entails: PreOrder Entails.
  Next Obligation.
  Proof.
    ii. ss.
  Qed.
  Next Obligation.
  Proof.
    ii. exploit (H r); et.
  Qed.

  Lemma equiv_Entails: ∀ P Q : iProp, P ≡ Q ↔ Entails P Q ∧ Entails Q P.
  Proof.
    econs.
    { ii. split; red; i; eapply H; et. }
    { split. des. i. split; i.
      { ii. exploit H0; et. }
      { ii. exploit H; et. }
    }
  Qed.

  Lemma Pure_ne: ∀ n : nat, Proper (iff ==> dist n) Pure.
  Proof.
    econs. i. split.
    { ii. eapply H. ss. }
    { ii. eapply H. ss. }
  Qed.

  Lemma And_ne: NonExpansive2 And.
  Proof.
    econs. i. split.
    { ii. inv H2. split.
      { eapply H; et. }
      { eapply H0; et. }
    }
    { ii. inv H2. split.
      { eapply H; et. }
      { eapply H0; et. }
    }
  Qed.

  Lemma Or_ne: NonExpansive2 Or.
  Proof.
    econs. i. split.
    { ii. inv H2.
      { left. eapply H; et. }
      { right. eapply H0; et. }
    }
    { ii. inv H2.
      { left. eapply H; et. }
      { right. eapply H0; et. }
    }
  Qed.

  Lemma Impl_ne: NonExpansive2 Impl.
  Proof.
    econs. i. split.
    { ii. eapply H0; et. eapply H2; et. eapply H; et. }
    { ii. eapply H0; et. eapply H2; et. eapply H; et. }
  Qed.

  Lemma Sepconj_ne: NonExpansive2 Sepconj.
  Proof.
    econs. i. split.
    { ii. inv H2. des. subst. eexists. esplits; eauto.
      { eapply H; et. eapply URA.wf_mon; et. }
      { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
    }
    { ii. inv H2. des. subst. eexists. esplits; eauto.
      { eapply H; et. eapply URA.wf_mon; et. }
      { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
    }
  Qed.

  Lemma Wand_ne: NonExpansive2 Wand.
  Proof.
    econs. i. split.
    { ii. exploit H2; et.
      { eapply H; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
      { i. eapply H0; et. }
    }
    { ii. exploit H2; et.
      { eapply H; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
      { i. eapply H0; et. }
    }
  Qed.

  Lemma Persistently_ne: NonExpansive Persistently.
  Proof.
    ii. ss.
  Qed.

  Lemma Univ_ne: ∀ (A : Type) (n : nat), Proper (pointwise_relation A (dist n) ==> dist n) Univ.
  Proof.
    econs. i. split.
    { ii. exploit H; et. i. eapply x2; et. }
    { ii. exploit H; et. i. eapply x2; et. }
  Qed.

  Lemma Ex_ne: ∀ (A : Type) (n : nat), Proper (pointwise_relation A (dist n) ==> dist n) Ex.
  Proof.
    econs. i. split.
    { ii. inv H1. exploit H; et. i. eexists. eapply x2; et. }
    { ii. inv H1. exploit H; et. i. eexists. eapply x2; et. }
  Qed.

  Lemma Pure_intro: ∀ (φ : Prop) (P : iProp), φ → Entails P (Pure φ).
  Proof.
    ii. ss.
  Qed.

  Lemma Pure_elim: ∀ (φ : Prop) (P : iProp), (φ → Entails (Pure True) P) → Entails (Pure φ) P.
  Proof.
    ii. eapply H in H0. eapply H0; ss.
  Qed.

  Lemma And_elim_l: ∀ P Q : iProp, Entails (And P Q) P.
  Proof.
    ii. eapply H.
  Qed.

  Lemma And_elim_r: ∀ P Q : iProp, Entails (And P Q) Q.
  Proof.
    ii. eapply H.
  Qed.

  Lemma And_intro: ∀ P Q R : iProp, Entails P Q → Entails P R → Entails P (And Q R).
  Proof.
    ii. split; et.
  Qed.

  Lemma Or_intro_l: ∀ P Q : iProp, Entails P (Or P Q).
  Proof.
    ii. left. ss.
  Qed.

  Lemma Or_intro_r: ∀ P Q : iProp, Entails Q (Or P Q).
  Proof.
    ii. right. ss.
  Qed.

  Lemma Or_elim: ∀ P Q R : iProp, Entails P R → Entails Q R → Entails (Or P Q) R.
  Proof.
    ii. inv H1.
    { eapply H; ss. }
    { eapply H0; ss. }
  Qed.

  Lemma Impl_intro_r: ∀ P Q R : iProp, Entails (And P Q) R → Entails P (Impl Q R).
  Proof.
    ii. eapply H; et. split; ss.
  Qed.

  Lemma Impl_elim_l: ∀ P Q R : iProp, Entails P (Impl Q R) → Entails (And P Q) R.
  Proof.
    ii. inv H0. eapply H; et.
  Qed.

  Lemma Univ_intro: ∀ (A : Type) (P : iProp) (Ψ : A → iProp), (∀ a : A, Entails P (Ψ a)) → Entails P (Univ (λ a : A, Ψ a)).
  Proof.
    ii. eapply H; et.
  Qed.

  Lemma Univ_elim: ∀ (A : Type) (Ψ : A → iProp) (a : A), Entails (Univ (λ a0 : A, Ψ a0)) (Ψ a).
  Proof.
    ii. eapply H; et.
  Qed.

  Lemma Ex_intro: ∀ (A : Type) (Ψ : A → iProp) (a : A), Entails (Ψ a) (Ex (λ a0 : A, Ψ a0)).
  Proof.
    ii. eexists. eauto.
  Qed.

  Lemma Ex_elim: ∀ (A : Type) (Φ : A → iProp) (Q : iProp), (∀ a : A, Entails (Φ a) Q) → Entails (Ex (λ a : A, Φ a)) Q.
  Proof.
    ii. inv H0. eapply H; et.
  Qed.

  Lemma Sepconj_mono: ∀ P P' Q Q' : iProp, Entails P Q → Entails P' Q' → Entails (Sepconj P P') (Sepconj Q Q').
  Proof.
    ii. unfold Sepconj in *. des; subst. esplits; et.
    { eapply H; et. eapply URA.wf_mon; et. }
    { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
  Qed.

  Lemma Emp_Sepconj_l: ∀ P : iProp, Entails P (Sepconj Emp P).
  Proof.
    ii. exists ε, r. splits; ss. rewrite URA.unit_idl. et.
  Qed.

  Lemma Emp_Sepconj_r: ∀ P : iProp, Entails (Sepconj Emp P) P.
  Proof.
    ii. inv H. des; subst. inv H1. rewrite URA.unit_idl. et.
  Qed.

  Lemma Sepconj_comm: ∀ P Q : iProp, Entails (Sepconj P Q) (Sepconj Q P).
  Proof.
    ii. unfold Sepconj in *. des. subst. exists b, a. splits; et. apply URA.add_comm.
  Qed.

  Lemma Sepconj_assoc: ∀ P Q R : iProp, Entails (Sepconj (Sepconj P Q) R) (Sepconj P (Sepconj Q R)).
  Proof.
    ii. unfold Sepconj in *. des; subst. esplits; [|apply H2| |apply H3|apply H1]; ss.
    rewrite URA.add_assoc. ss.
  Qed.

  Lemma Wand_intro_r: ∀ P Q R : iProp, Entails (Sepconj P Q) R → Entails P (Wand Q R).
  Proof.
    ii. eapply H; et. exists r, rp. splits; et.
  Qed.

  Lemma Wand_elim_l: ∀ P Q R : iProp, Entails P (Wand Q R) → Entails (Sepconj P Q) R.
  Proof.
    ii. unfold Sepconj in *. des; subst. eapply H; et. eapply URA.wf_mon; et.
  Qed.

  Lemma Persistently_mono: ∀ P Q : iProp, Entails P Q → Entails (Persistently P) (Persistently Q).
  Proof.
    ii. ss.
  Qed.

  Lemma Persistently_idemp: ∀ P : iProp, Entails (Persistently P) (Persistently (Persistently P)).
  Proof.
    ii. ss.
  Qed.

  Lemma Persistently_Univ: ∀ (A : Type) (Ψ : A → iProp), Entails (Univ (λ a : A, id (Ψ a))) ((Univ (λ a : A, Ψ a))).
  Proof.
    ii. ss.
  Qed.

  Lemma Persistently_Ex: ∀ (A : Type) (Ψ : A → iProp), Entails (id (Ex (λ a : A, Ψ a))) (Ex (λ a : A, id (Ψ a))).
  Proof.
    ii. ss.
  Qed.

  Lemma Persistently_Sepconj: ∀ P Q : iProp, Entails (Sepconj (Persistently P) Q) (Persistently P).
  Proof.
    ii. unfold Sepconj in *. des; subst. ss.
  Qed.

  Lemma Persistently_And: ∀ P Q : iProp, Entails (And (Persistently P) Q) (Sepconj P Q).
  Proof.
    ii. inv H. ss.
  Qed.

  Lemma uPred_bi_mixin:
    BiMixin
      Entails Emp Pure And Or Impl
      (@Univ) (@Ex) Sepconj Wand
      Persistently.
  Proof.
    econs.
    - exact PreOrder_Entails.
    - exact equiv_Entails.
    - exact Pure_ne.
    - exact And_ne.
    - exact Or_ne.
    - exact Impl_ne.
    - exact Univ_ne.
    - exact Ex_ne.
    - exact Sepconj_ne.
    - exact Wand_ne.
    - exact Persistently_ne.
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
    - exact Persistently_mono.
    - exact Persistently_idemp.
    - ii. ss.

  : ∀ P : iProp, Entails (Persistently P) (Persistently (Persistently P)).
  Proof.
    ii. ss.
  Qed.

  Lemma Persistently_Univ: ∀ (A : Type) (Ψ : A → iProp), Entails (Univ (λ a : A, id (Ψ a))) ((Univ (λ a : A, Ψ a))).
  Proof.
    ii. ss.
  Qed.

  Lemma Persistently_Ex: ∀ (A : Type) (Ψ : A → iProp), Entails (id (Ex (λ a : A, Ψ a))) (Ex (λ a : A, id (Ψ a))).
  Proof.
    ii. ss.
  Qed.

  Lemma Persistently_Sepconj: ∀ P Q : iProp, Entails (Sepconj (Persistently P) Q) (Persistently P).
  Proof.
    ii. unfold Sepconj in *. des; subst. ss.
  Qed.

  Lemma Persistently_And: ∀ P Q : iProp, Entails (And (Persistently P) Q) (Sepconj P Q).
  Proof.
    ii. inv H. ss.
  Qed.



  Admitted.


(*   NonExpansive id *)

(* subgoal 2 (ID 95) is: *)
(*  ∀ P Q : iProp, Entails P Q → Entails (id P) (id Q) *)
(* subgoal 3 (ID 96) is: *)
(*  ∀ P : iProp, Entails P (id P) *)
(* subgoal 4 (ID 97) is: *)
(*  ∀ (A : Type) (Φ : A → iProp), Entails (Univ (λ a : A, id (Φ a))) (id (Univ (λ a : A, Φ a))) *)
(* subgoal 5 (ID 98) is: *)
(*  ∀ (A : Type) (Φ : A → iProp), Entails (id (Ex (λ a : A, Φ a))) (Or (id (Pure False)) (Ex (λ a : A, id (Φ a)))) *)
(* subgoal 6 (ID 99) is: *)
(*  ∀ P Q : iProp, Entails (id (Sepconj P Q)) (Sepconj (id P) (id Q)) *)
(* subgoal 7 (ID 100) is: *)
(*  ∀ P Q : iProp, Entails (Sepconj (id P) (id Q)) (id (Sepconj P Q)) *)
(* subgoal 8 (ID 101) is: *)
(*  ∀ P : iProp, Entails (id (id P)) (id (id P)) *)
(* subgoal 9 (ID 102) is: *)
(*  ∀ P : iProp, Entails (id (id P)) (id (id P)) *)
(* subgoal 10 (ID 103) is: *)
(*  ∀ P : iProp, Entails (id P) (Or (id (Pure False)) (Impl (id (Pure False)) P)) *)

(*   NonExpansive bupd *)

(* subgoal 2 (ID 97) is: *)
(*  ∀ P : uPredI M, P -∗ |==> P *)
(* subgoal 3 (ID 98) is: *)
(*  ∀ P Q : uPredI M, (P -∗ Q) → (|==> P) -∗ |==> Q *)
(* subgoal 4 (ID 99) is: *)
(*  ∀ P : uPredI M, (|==> |==> P) -∗ |==> P *)
(* subgoal 5 (ID 100) is: *)
(*  ∀ P R : uPredI M, (|==> P) ∗ R -∗ |==> P ∗ R *)

End IRIS.


Section cofe.
  Context {M : GRA.t}.

  Inductive uPred_equiv' (P Q : iProp) : Prop :=
    { uPred_in_equiv : ∀ x, URA.wf x -> Upd P x <-> Upd Q x }.

  Local Instance uPred_equiv : Equiv iProp := uPred_equiv'.
  Definition uPred_dist' (n : nat) (P Q : iProp) : Prop := uPred_equiv' P Q.
  Local Instance uPred_dist : Dist iProp := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin iProp.
  Proof.
    split.
    - intros P Q; split.
      + ii. ss.
      + ii. specialize (H 0). ss.
    - i. split.
      + ii. ss.
      + ii. econs. i. symmetry. apply H. auto.
      + ii. econs. i. transitivity (Upd y x0); [apply H|apply H0]; ss.
    - i. ss.
  Qed.
  Canonical Structure uPredO : ofe := Ofe iProp uPred_ofe_mixin.

  Program Definition uPred_compl : Compl uPredO := λ c x, forall n, Upd (c n) x.

  Global Program Instance uPred_cofe : Cofe uPredO := {| compl := uPred_compl |}.
  Next Obligation.
    econs. i. split.
    - ii. exploit H0; et. i. des.
      specialize (x1 n). exploit x1; et.
    - ii. exists x. esplits; et.
      ii. destruct (le_ge_dec n n0).
      + apply c in l. apply l in H0; et.
      + apply c in g. apply g in H0; et.
  Qed.
End cofe.
Global Arguments uPredO : clear implicits.


Lemma uPred_bi_mixin (M : GRA.t) :
  BiMixin
    Entails Emp Pure And Or Impl
    (@Univ _) (@Ex _) Sepconj Wand
    id.
Proof.
Admitted.

Lemma uPred_bi_later_mixin (M : GRA.t) :
  BiLaterMixin
    Entails Pure Or Impl
    (@Univ _) (@Ex _) Sepconj id id.
Proof.
Admitted.

Canonical Structure uPredI (M : GRA.t) : bi :=
  {| bi_bi_mixin := uPred_bi_mixin M;
     bi_bi_later_mixin := uPred_bi_later_mixin M |}.

Global Instance uPred_pure_forall M : BiPureForall (uPredI M).
Proof.
  ii. exists r. splits; et.
Qed.

(** extra BI instances *)

Global Instance uPred_affine M : BiAffine (uPredI M) | 0.
Proof.
  ii. exists r. esplits; et. ss.
Qed.
Global Hint Immediate uPred_affine : core.

(** Re-state/export lemmas about Iris-specific primitive connectives (own, valid) *)

Module uPred.

Section restate.
Context {M : GRA.t}.
Implicit Types φ : Prop.
Implicit Types P Q : iProp.
Implicit Types A : Type.

(* Force implicit argument M *)
Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P%I Q%I).
Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).

(** Re-exporting primitive lemmas that are not in any interface *)
Lemma ownM_op (a1 a2 : M) :
  Own (a1 ⋅ a2) ⊣⊢ Own a1 ∗ Own a2.
Proof. Admitted.
Lemma ownM_unit P : P ⊢ (Own ε).
Proof. Admitted.
Lemma bupd_ownM_updateP x (Φ : M → Prop) :
  URA.updatable_set x Φ → Own x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ Own y.
Proof. Admitted.

Lemma ownM_valid (a : M) : Own a ⊢ Pure (URA.wf a).
Proof. Admitted.
Lemma cmra_valid_intro P (a : M) : URA.wf a → P ⊢ Pure (URA.wf a).
Proof. Admitted.
Lemma cmra_valid_weaken (a b : M) : Pure (URA.wf (a ⋅ b)) ⊢ Pure (URA.wf a).
Proof. Admitted.

(** This is really just a special case of an entailment
between two [siProp], but we do not have the infrastructure
to express the more general case. This temporary proof rule will
be replaced by the proper one eventually. *)
Lemma valid_entails (a b : M) :
  URA.wf a → URA.wf b → Pure (URA.wf a) ⊢ Pure (URA.wf b).
Proof. Admitted.

(** Consistency/soundness statement *)
Lemma pure_soundness φ : (⊢@{uPredI M} ⌜ φ ⌝) → φ.
Proof. Admitted.

End restate.

End uPred.

From iris.proofmode Require Export tactics.

Goal forall `{M : GRA.t} (P Q: iProp), Sepconj P (Upd Q) ⊢ Upd P.
Proof.
  i. iStartProof. iIntros "[Hxs Hys]". iMod "Hxs". iApply "Hxs".
Qed.
