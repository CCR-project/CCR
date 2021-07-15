Require Import Coqlib.
Require Import ITreelib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.

Set Implicit Arguments.
From ITree Require Import Recursion.

Definition infloop {E R S} (body: itree E R): itree E S :=
  (rec (fun _ => resum_itr body;;; trigger (Call tt)) tt).

(* Set Printing All. *)
(* eutt_interp *)
(* (@eq2 (forall _ : Type, Type) Handler Eq2_Handler E F) *)
Global Program Instance rec_eutt {E A B}:
  (* Proper (eq2 ==> eq ==> Eq.eutt eq) (@rec E A B). *)
  Proper ((fun x y => forall a, x a ≈ y a) ==> eq ==> Eq.eutt eq) (@rec E A B).
Next Obligation.
  ii. subst. rename y0 into a. unfold rec, mrec, interp_mrec. ss.
  (* assert(T:=@eutt_iter). unfold CategoryOps.iter, Iter_Kleisli, Basics.iter, MonadIter_itree in T. *)
  (* specialize (T E B (itree (sum1 (callE A B) E) B)). rr in T. unfold pointwise_relation in *. *)
  (* Fail eapply T. *)
  (*** we need eutt, but it is eq. See the proof of `eutt_iter`;
       it is just an instance `(eutt_iter' eq)` ***)

  eapply eutt_iter_gen; cycle 1.
  { apply H. }
  ii. eapply eqit_mon with (RR:=eq); et.
  { ii. subst. refl. }
  fold (@eutt E _ _ (@eq (sum (itree (sum1 (callE A B) E) B) B))).
Abort.
Next Obligation.
  ii. subst. rename y0 into a. unfold rec, mrec, interp_mrec. ss.

  (* eapply eutt_iter'; cycle 1. *)
  (* { instantiate (1:=Eq.eutt eq). ss. } *)
  (* i. des_ifs; ss. *)
  (* - pfold. econs. *)
  (* revert a. *)
  unfold rec. unfold mrec. ss.
  ginit.
  gcofix CIH.
  ii.
  eapply geuttgen_cong_eqit; et. Undo 1.
  guclo eqit_clo_trans. econs; et. Undo 1.
  (* eapply geuttgen_cong_eqit; et. *)
Abort.
Next Obligation.
  ii. subst. rename y0 into a. unfold rec, mrec. ss.
  eapply Proper_interp_mrec; et.
  ii. destruct a0; ss.
Qed.

Goal (infloop (E:=void1) (S:=void) (Ret 1)) ≈ (infloop (tau;; Ret 1)).
Proof.
  unfold infloop. f_equiv. ii.
  Local Transparent resum_itr.
  unfold resum_itr. repeat (try rewrite ! interp_ret; try rewrite ! interp_tau). irw.
  rewrite tau_eutt. refl.
Qed.
