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
  Definition Upd (P: iProp): iProp := fun r0 => forall ctx, URA.wf (r0 ⋅ ctx) -> exists r1, URA.wf (r1 ⋅ ctx) /\ P r1.

  Definition Entails (P Q: iProp): Prop := forall r (WF: URA.wf r), P r -> Q r.
  Definition Equival (P Q: iProp): Prop := Entails P Q /\ Entails Q P.
  Definition Impure (P: iProp): Prop := P ε.

  Definition Emp `{M: GRA.t} : iProp := Pure True.
End IRIS.


Section cofe.
  Context {M : GRA.t}.

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
    - i. apply H0.
    - ii. destruct (le_ge_dec n n0).
      + apply c in l. apply l; auto.
      + apply c in g. apply g; auto.
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
Proof. Admitted.

Lemma uPred_bupd_mixin M : BiBUpdMixin (uPredI M) Upd.
Proof. Admitted.
Global Instance uPred_bi_bupd M : BiBUpd (uPredI M) := {| bi_bupd_mixin := uPred_bupd_mixin M |}.

(** extra BI instances *)

Global Instance uPred_affine M : BiAffine (uPredI M) | 0.
Proof. Admitted.
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

Goal forall `{M : GRA.t} (P Q: iProp), Sepconj P Q ⊢ P.
Proof.
  i. iStartProof. iIntros "[Hxs Hys]". iApply "Hxs".
Qed.
