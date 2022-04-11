Require Import HoareDef MutHeader MutF0 MutF1 SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import HTactics ProofMode.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    mk_wf (fun (_: unit) _ _ => (True: iProp)%I).

  Ltac check_o :=
    match goal with
    | [ |- (gpaco8 _ _ _ _ _ _ _ ?o_src ?o_tgt _ _ _) ] =>
      pose o_src; pose o_tgt
    end.

  Theorem correct: refines2 [MutF0.F] [MutF1.F].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et.
    { ss. }
    2: { exists tt. econs; ss; rr; uipropall. }
    econs; ss. init. harg. mDesAll.
    des; clarify. unfold fF, ccallU. steps. astart 10.
    force_r.
    { eapply mut_max_intrange. auto. } steps.
    destruct (dec (Z.of_nat x) 0%Z).
    - destruct x; ss. astop. steps. force_l. eexists. steps.
      hret _; ss.
    - destruct x; [ss|]. rewrite Nat2Z.inj_succ. steps.
      acatch. hcall _ _ with "*"; auto.
      { iPureIntro.
        replace (Z.succ (Z.of_nat x) - 1)%Z with (Z.of_nat x) by lia.
        esplits; et. lia. }
      { splits; ss; eauto with ord_step. }
      i. mDesAll. des; clarify.
      steps. astop. steps.
      force_l. eexists. steps.
      hret _; ss. iPureIntro. esplits; ss.
      f_equal. f_equal. lia.
      Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
