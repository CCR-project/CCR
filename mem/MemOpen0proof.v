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

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Let wf: W -> Prop :=
    @mk_wf
      _ unit
      top4
      (fun _ _mem_src0 _mem_tgt0 => ⌜_mem_src0 = _mem_tgt0⌝)%I
  .

  Variable sk: Sk.t.

  Theorem correct: ModSemPair.sim (Mem0.MemSem sk) (SModSem.to_src (MemOpen.SMemSem sk)).
  Proof.
   econstructor 1 with (wf:=wf); et; swap 2 3.
    { ss. econs; ss. red. uipropall. }





    econs; ss.
    { unfold allocF, fun_to_src, body_to_src, cfun, KModSem.transl_fun. init.
      destruct (Any.split varg) eqn:T.
      { cbn. steps. }
      steps. inv WF. rr in RTGT. uipropall. clarify. clear_fast.
      apply_all_once Any.downcast_upcast. des; clarify. rewrite Any.upcast_downcast in *. steps.
      des_ifs.
      { steps. force_l. esplits; et. steps.
        rr. econs; ss. rr. uipropall. }
      { steps. }
    }
    econs; ss.
    { unfold freeF, fun_to_src, body_to_src, cfun, KModSem.transl_fun. init.
      destruct (Any.split varg) eqn:T.
      { cbn. steps. }
      steps. inv WF. rr in RTGT. uipropall. clarify. clear_fast.
      apply_all_once Any.downcast_upcast. des; clarify. rewrite Any.upcast_downcast in *. steps.
      force_r; ss. steps.
      rr. econs; ss. rr. uipropall.
    }
    econs; ss.
    { unfold loadF, fun_to_src, body_to_src, cfun, KModSem.transl_fun. init.
      destruct (Any.split varg) eqn:T.
      { cbn. steps. }
      steps. inv WF. rr in RTGT. uipropall. clarify. clear_fast.
      apply_all_once Any.downcast_upcast. des; clarify. rewrite Any.upcast_downcast in *. steps.
      force_r; ss. steps.
      rr. econs; ss. rr. uipropall.
    }
    econs; ss.
    { unfold storeF, fun_to_src, body_to_src, cfun, KModSem.transl_fun. init.
      destruct (Any.split varg) eqn:T.
      { cbn. steps. }
      steps. inv WF. rr in RTGT. uipropall. clarify. clear_fast.
      apply_all_once Any.downcast_upcast. des; clarify. rewrite Any.upcast_downcast in *. steps.
      force_r; ss. steps.
      rr. econs; ss. rr. uipropall.
    }
    econs; ss.
    { unfold cmpF, fun_to_src, body_to_src, cfun, KModSem.transl_fun. init.
      destruct (Any.split varg) eqn:T.
      { cbn. steps. }
      steps. inv WF. rr in RTGT. uipropall. clarify. clear_fast.
      apply_all_once Any.downcast_upcast. des; clarify. rewrite Any.upcast_downcast in *. steps.
      force_r; ss. steps.
      des_ifs; steps.
      { rr. econs; ss. rr. uipropall. }
      { rr. econs; ss. rr. uipropall. }
    }
  Qed.

End SIMMODSEM.
