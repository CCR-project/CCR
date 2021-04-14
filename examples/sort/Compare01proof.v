Require Import HoareDef Compare0 Compare1 SimModSemL SimModSem.
Require Import Coqlib.
Require Import Universe.
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

Require Import HTactics Logic YPM.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.




Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = (ε, tt↑)>>) /\
      (<<TGT: mrps_tgt0 = (ε, tt↑)>>)
  .

  Theorem correct: ModPair.sim (Compare1.Main cmpspecs) Compare0.Compare.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf); et; ss.
    econs; ss; [|econs; ss; [|econs; ss]].
    - init. unfold mainF, ccall. harg_tac. des; subst. iRefresh.
      rewrite Any.upcast_downcast. ss. steps.
      force_l. eexists. steps. ss.

      r
 anytac.


econs; ss.  ii. init.

admit "". admit "". econs. init. unfold ccall.
    harg_tac. des; clarify. unfold fF, ccall. anytac. ss.
    steps. astart 10. destruct (dec (Z.of_nat x) 0%Z).
    - destruct x; ss. astop.
      force_l. eexists. hret_tac (@URA.unit Σ) (@URA.unit Σ).
      { esplits; eauto. }
      { split; auto. }
    - destruct x; [ss|]. rewrite Nat2Z.inj_succ. steps.
      acall_tac x (ord_pure x) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ).
      { replace (Z.succ (Z.of_nat x) - 1)%Z with (Z.of_nat x) by lia. ss. }
      { splits; ss. auto with ord_step. }
      { split; auto. }
      des. subst. anytac. asimpl. steps. astop.
      force_l. eexists. hret_tac (@URA.unit Σ) (@URA.unit Σ).
      { splits; auto. unfold sum. splits; auto. ss. repeat f_equal. lia. }
      { split; ss. }
  Qed.

End SIMMODSEM.
