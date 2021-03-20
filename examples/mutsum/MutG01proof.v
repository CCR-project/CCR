Require Import HoareDef MutHeader MutG0 MutG1 SimModSem.
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



(* TODO: move to SimModSem & add cpn3_wcompat *)
Hint Resolve sim_itree_mon: paco.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = Maps.add "G" (ε, tt↑) Maps.empty>>) /\
      (<<TGT: mrps_tgt0 = Maps.add "G" (ε, tt↑) Maps.empty>>)
  .

  Theorem correct: ModSemPair.sim MutG1.GSem MutG0.GSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss. init. unfold ccall, interp_hCallE_tgt.
    harg_tac. des; clarify. unfold gF, ccall. anytac. ss. unfold APC. steps.
    destruct (dec (Z.of_nat x) 0%Z).
    - destruct x; ss. force_l. exists 0. steps.
      force_l. eexists. hret_tac (@URA.unit Σ) (@URA.unit Σ).
      { esplits; eauto. }
      { split; auto. }
    - destruct x; [ss|]. rewrite Nat2Z.inj_succ.
      force_l. exists 1. steps. force_l. exists false.
      steps. force_l. eexists ("f", [Vint (Z.of_nat x)]↑).
      steps. anytac.
      hcall_tac x (ord_pure x) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ).
      { replace (Z.succ (Z.of_nat x) - 1)%Z with (Z.of_nat x) by lia.
        splits; auto. }
      { splits; ss. }
      { split; auto. }
      des; subst. anytac. asimpl.
      steps. force_l. eexists. hret_tac (@URA.unit Σ) (@URA.unit Σ).
      { splits; auto. unfold sum. splits; auto. ss. repeat f_equal. lia. }
      { split; ss. }
  Qed.

End SIMMODSEM.
