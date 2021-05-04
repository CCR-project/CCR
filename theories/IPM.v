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
  Definition Upd (P: iProp): iProp := fun r0 => forall ctx, URA.wf (r0 ⋅ ctx) -> exists r1, URA.wf (r1 ⋅ ctx) /\ P r1.

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
  Definition Wand (P Q: iProp): iProp := fun r => forall rp, URA.wf (r ⋅ rp) -> P rp -> Upd Q (r ⋅ rp).

  Definition Entails (P Q: iProp): Prop := forall r (WF: URA.wf r), P r -> Upd Q r.
  Definition Impure (P: iProp): Prop := P ε.

  Definition Emp `{M: GRA.t} : iProp := Pure True.

  (* Trivial Ofe Structure *)
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


  (* BI axioms *)

  Lemma PreOrder_Entails: PreOrder Entails.
  Proof.
    econs.
    { ii. exists r. splits; et. }
    { ii. exploit (H r); et. i. des.
      exploit (H0 r1); et. eapply URA.wf_mon; et. }
  Qed.

  Lemma equiv_Entails: ∀ P Q : iProp, P ≡ Q ↔ Entails P Q ∧ Entails Q P.
  Proof.
    econs.
    { ii. split; red; i; eapply H; et.
      { ii. exists r. splits; et. }
      { ii. exists r. splits; et. }
    }
    { split. des. i. split; i.
      { ii. exploit H2; et. i. des.
        exploit (H r1); et. eapply URA.wf_mon; et. }
      { ii. exploit H2; et. i. des.
        exploit (H0 r1); et. eapply URA.wf_mon; et. }
    }
  Qed.

  Lemma Pure_ne: ∀ n : nat, Proper (iff ==> dist n) Pure.
  Proof.
    econs. i. split.
    { ii. exploit H1; et. i. des. esplits; et. eapply H. ss. }
    { ii. exploit H1; et. i. des. esplits; et. eapply H3. ss. }
  Qed.

  Goal ∀ P Q R : iProp, Entails P Q → Entails P R → Entails P (And Q R).
  Proof.
    i. unfold Entails, And in *. ii.
    exploit (H r); et. i. des.
    exploit (H0 r); et. i. des.

  Lemma And_ne: NonExpansive2 And.
  Proof.
    econs. i. split.
    { ii. exploit H2; et. i. des. esplits ;et.
      inv x3. split; auto.
      { inv H.

        eapply H. red in H. red in H. red in H. red in H. eapply H.

      inv H2.

(* subgoal 4 (ID 40) is: *)
(*  NonExpansive2 And *)
(* subgoal 5 (ID 41) is: *)
(*  NonExpansive2 Or *)
(* subgoal 6 (ID 42) is: *)
(*  NonExpansive2 Impl *)
(* subgoal 7 (ID 43) is: *)
(*  ∀ (A : Type) (n : nat), Proper (pointwise_relation A (dist n) ==> dist n) Univ *)
(* subgoal 8 (ID 44) is: *)
(*  ∀ (A : Type) (n : nat), Proper (pointwise_relation A (dist n) ==> dist n) Ex *)
(* subgoal 9 (ID 45) is: *)
(*  NonExpansive2 Sepconj *)
(* subgoal 10 (ID 46) is: *)
(*  NonExpansive2 Wand *)
(* subgoal 11 (ID 47) is: *)
(*  NonExpansive id *)
(* subgoal 12 (ID 48) is: *)
(*  ∀ (φ : Prop) (P : iProp), φ → Entails P (Pure φ) *)
(* subgoal 13 (ID 49) is: *)
(*  ∀ (φ : Prop) (P : iProp), (φ → Entails (Pure True) P) → Entails (Pure φ) P *)
(* subgoal 14 (ID 50) is: *)
(*  ∀ P Q : iProp, Entails (And P Q) P *)
(* subgoal 15 (ID 51) is: *)
(*  ∀ P Q : iProp, Entails (And P Q) Q *)
(* subgoal 16 (ID 52) is: *)
(*  ∀ P Q R : iProp, Entails P Q → Entails P R → Entails P (And Q R) *)
(* subgoal 17 (ID 53) is: *)
(*  ∀ P Q : iProp, Entails P (Or P Q) *)
(* subgoal 18 (ID 54) is: *)
(*  ∀ P Q : iProp, Entails Q (Or P Q) *)
(* subgoal 19 (ID 55) is: *)
(*  ∀ P Q R : iProp, Entails P R → Entails Q R → Entails (Or P Q) R *)
(* subgoal 20 (ID 56) is: *)
(*  ∀ P Q R : iProp, Entails (And P Q) R → Entails P (Impl Q R) *)
(* subgoal 21 (ID 57) is: *)
(*  ∀ P Q R : iProp, Entails P (Impl Q R) → Entails (And P Q) R *)
(* subgoal 22 (ID 58) is: *)
(*  ∀ (A : Type) (P : iProp) (Ψ : A → iProp), (∀ a : A, Entails P (Ψ a)) → Entails P (Univ (λ a : A, Ψ a)) *)
(* subgoal 23 (ID 59) is: *)
(*  ∀ (A : Type) (Ψ : A → iProp) (a : A), Entails (Univ (λ a0 : A, Ψ a0)) (Ψ a) *)
(* subgoal 24 (ID 60) is: *)
(*  ∀ (A : Type) (Ψ : A → iProp) (a : A), Entails (Ψ a) (Ex (λ a0 : A, Ψ a0)) *)
(* subgoal 25 (ID 61) is: *)
(*  ∀ (A : Type) (Φ : A → iProp) (Q : iProp), (∀ a : A, Entails (Φ a) Q) → Entails (Ex (λ a : A, Φ a)) Q *)
(* subgoal 26 (ID 62) is: *)
(*  ∀ P P' Q Q' : iProp, Entails P Q → Entails P' Q' → Entails (Sepconj P P') (Sepconj Q Q') *)
(* subgoal 27 (ID 63) is: *)
(*  ∀ P : iProp, Entails P (Sepconj Emp P) *)
(* subgoal 28 (ID 64) is: *)
(*  ∀ P : iProp, Entails (Sepconj Emp P) P *)
(* subgoal 29 (ID 65) is: *)
(*  ∀ P Q : iProp, Entails (Sepconj P Q) (Sepconj Q P) *)
(* subgoal 30 (ID 66) is: *)
(*  ∀ P Q R : iProp, Entails (Sepconj (Sepconj P Q) R) (Sepconj P (Sepconj Q R)) *)
(* subgoal 31 (ID 67) is: *)
(*  ∀ P Q R : iProp, Entails (Sepconj P Q) R → Entails P (Wand Q R) *)
(* subgoal 32 (ID 68) is: *)
(*  ∀ P Q R : iProp, Entails P (Wand Q R) → Entails (Sepconj P Q) R *)
(* subgoal 33 (ID 69) is: *)
(*  ∀ P Q : iProp, Entails P Q → Entails (id P) (id Q) *)
(* subgoal 34 (ID 70) is: *)
(*  ∀ P : iProp, Entails (id P) (id (id P)) *)
(* subgoal 35 (ID 71) is: *)
(*  Entails Emp (id Emp) *)
(* subgoal 36 (ID 72) is: *)
(*  ∀ (A : Type) (Ψ : A → iProp), Entails (Univ (λ a : A, id (Ψ a))) (id (Univ (λ a : A, Ψ a))) *)
(* subgoal 37 (ID 73) is: *)
(*  ∀ (A : Type) (Ψ : A → iProp), Entails (id (Ex (λ a : A, Ψ a))) (Ex (λ a : A, id (Ψ a))) *)
(* subgoal 38 (ID 74) is: *)
(*  ∀ P Q : iProp, Entails (Sepconj (id P) Q) (id P) *)
(* subgoal 39 (ID 75) is: *)
(*  ∀ P Q : iProp, Entails (And (id P) Q) (Sepconj P Q) *)

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
