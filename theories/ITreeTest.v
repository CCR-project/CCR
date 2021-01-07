Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
Require Import Ordinal ClassicalOrdinal.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.
From ITree Require Import Recursion.

Definition infloop {E R S} (body: itree E R): itree E S :=
  (rec (fun _ => resum_itr body;; trigger (Call tt)) tt).

Lemma interp_ret :
forall {E F : Type -> Type} {R : Type} {f : forall T : Type, E T -> itree F T} (x : R),
interp f (Ret x) = Ret x. Proof. i. f. apply interp_ret. Qed.
Lemma interp_tau :
forall {E F : Type -> Type} {R : Type} {f : forall T : Type, E T -> itree F T} (t : itree E R),
interp f (tau;; t) = (tau;; interp f t). Proof. i. f. apply interp_tau. Qed.
(* Set Printing All. *)
(* eutt_interp *)
(* (@eq2 (forall _ : Type, Type) Handler Eq2_Handler E F) *)
Global Program Instance rec_eutt {E A B}:
  (* Proper (eq2 ==> eq ==> Eq.eutt eq) (@rec E A B). *)
  Proper ((fun x y => forall a, x a ≈ y a) ==> eq ==> Eq.eutt eq) (@rec E A B).
Next Obligation.
  ii. subst. rename y0 into a. revert a.
  unfold rec. unfold mrec. ss.
  ginit.
  gcofix CIH.
  ii.
  eapply geuttgen_cong_eqit; et. Undo 1.
  guclo eqit_clo_trans. econs; et. Undo 1.
  (* eapply geuttgen_cong_eqit; et. *)
  admit "".
Qed.

Goal (infloop (E:=void1) (S:=void) (Ret 1)) ≈ (infloop (tau;; Ret 1)).
Proof.
  unfold infloop.
  rewrite ! RecursionFacts.rec_as_interp.
  unfold resum_itr. repeat (try rewrite ! interp_ret; try rewrite ! interp_tau). irw.
  eapply InterpFacts.eutt_interp.
  - ii. destruct a; ss. destruct c; ss. destruct u; ss.
    rewrite ! RecursionFacts.rec_as_interp.
    repeat (try rewrite ! interp_ret; try rewrite ! interp_tau); irw.
    rewrite tau_eutt.
    admit "idk".
  - rewrite tau_eutt. refl.
Qed.

Goal (infloop (E:=void1) (S:=void) (Ret 1)) ≈ (infloop (tau;; Ret 1)).
Proof.
  unfold infloop. f_equiv. ii.
  unfold resum_itr. repeat (try rewrite ! interp_ret; try rewrite ! interp_tau). irw.
  rewrite tau_eutt. refl.
Qed.
