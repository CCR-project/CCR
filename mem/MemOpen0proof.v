Require Import Mem0 Mem1 MemOpen HoareDef SimModSem.
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
Require Import TODOYJ.
Require Import OpenDef HTactics Logic IPM.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    fun (_: unit) '(mem_src0, mem_tgt0) => mem_src0 = mem_tgt0.

  Variable sk: Sk.t.
  Variable frds: list mname.

  Theorem correct: ModSemPair.sim (Mem0.MemSem sk) (KModSem.transl_src frds (MemOpen.KMemSem sk)).
  Proof.
   econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { ss. }
    { esplits. ss. }





    econs; ss.
    { unfold allocF, fun_to_src, body_to_src, cfunU, KModSem.disclose_ksb_src, KModSem.body_to_src. init.
      match goal with | |- context[my_if ?b _ _] => destruct b eqn:T end.
      { cbn. steps. }
      steps. inv WF.
      apply_all_once Any.downcast_upcast. des; clarify. rewrite Any.upcast_downcast in *. steps.
      des_ifs.
      { steps. force_l. esplits; et. steps.
        red. esplits; et. rr. econs; ss. }
      { steps. }
    }
    econs; ss.
    { unfold freeF, fun_to_src, body_to_src, cfunU, KModSem.disclose_ksb_src, KModSem.body_to_src. init.
      match goal with | |- context[my_if ?b _ _] => destruct b eqn:T end.
      { cbn. steps. }
      steps. inv WF.
      apply_all_once Any.downcast_upcast. des; clarify. rewrite Any.upcast_downcast in *. steps.
      force_r; ss. steps.
      red. esplits; et. rr. econs; ss. 
    }
    econs; ss.
    { unfold loadF, fun_to_src, body_to_src, cfunU, KModSem.disclose_ksb_src, KModSem.body_to_src. init.
      match goal with | |- context[my_if ?b _ _] => destruct b eqn:T end.
      { cbn. steps. }
      steps. inv WF.
      apply_all_once Any.downcast_upcast. des; clarify. rewrite Any.upcast_downcast in *. steps.
      force_r; ss. steps.
      red. esplits; et. rr. econs; ss.
    }
    econs; ss.
    { unfold storeF, fun_to_src, body_to_src, cfunU, KModSem.disclose_ksb_src, KModSem.body_to_src. init.
      match goal with | |- context[my_if ?b _ _] => destruct b eqn:T end.
      { cbn. steps. }
      steps. inv WF.
      apply_all_once Any.downcast_upcast. des; clarify. rewrite Any.upcast_downcast in *. steps.
      force_r; ss. steps.
      red. esplits; et. rr. econs; ss.
    }
    econs; ss.
    { unfold cmpF, fun_to_src, body_to_src, cfunU, KModSem.disclose_ksb_src, KModSem.body_to_src. init.
      match goal with | |- context[my_if ?b _ _] => destruct b eqn:T end.
      { cbn. steps. }
      steps. inv WF. 
      apply_all_once Any.downcast_upcast. des; clarify. rewrite Any.upcast_downcast in *. steps.
      force_r; ss. steps.
      des_ifs; steps.
      { red. esplits; et. rr. econs; ss. }
      { red. esplits; et. rr. econs; ss. }
    }
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.
