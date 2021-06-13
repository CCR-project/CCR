Require Import NewStack1 NewStack2 HoareDef SimModSem.
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
Require Import HTactics Logic IPM.
Require Import OpenDef.
Require Import TODO.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Let wf: W -> Prop :=
    @mk_wf _ unit
           (fun _ mp_src mp_tgt => ⌜mp_src = mp_tgt⌝%I)
           top4
  .

  Theorem sim_modsem: ModSemPair.sim (NewStack2.StackSem) (SModSem.to_src NewStack1.SStackSem).
  Proof.
    econstructor 1 with (wf:=wf); ss; et; swap 2 3.
    { econs; ss.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iPureIntro. ss.
    }
    assert(BDOOR: interp_hCallE_src (KModSem.transl_itr_tgt APCK) = Ret tt).
    { admit "mid - BDOOR". }
    econs; ss.
    { init. inv WF. rr in RSRC. uipropall. subst. clear_fast.
      unfold cfun2, fun_to_src, body_to_src, KModSem.transl_fun_tgt, cfun, new_body, NewStack1.new_body.
      steps.
      destruct (Any.split varg) eqn:T.
      - cbn. des_ifs. steps. rewrite BDOOR. steps.
        force_l. esplits. steps. rewrite _UNWRAPN0. steps. rewrite _GUARANTEE. force_l; ss. steps.
        econs; ss; et. rr. uipropall; ss.
      - cbn. des_ifs. steps. rewrite BDOOR. steps.
        force_l. esplits. steps. rewrite _UNWRAPN0. steps. rewrite _GUARANTEE. force_l; ss. steps.
        econs; ss; et. rr. uipropall; ss.
    }
    econs; ss.
    { init. inv WF. rr in RSRC. uipropall. subst. clear_fast.
      unfold cfun2, fun_to_src, body_to_src, KModSem.transl_fun_tgt, cfun, pop_body, NewStack1.pop_body.
      steps.
      destruct (Any.split varg) eqn:T.
      - cbn. des_ifs. steps. rewrite BDOOR. steps.
        des_ifs.
        { steps. econs; ss; et. rr. uipropall; ss. rewrite Any.upcast_downcast in *. clarify.
          rewrite insert_delete. rewrite insert_id; ss. sym. eapply Any.downcast_upcast; ss.
        }
        steps. gstep; econs; ss; et.
        { econs; ss; et. rr. uipropall; ss. rewrite Any.upcast_downcast in *. clarify.
          f_equal. rewrite insert_delete; ss. }
        ii. exists 100. steps.
      - cbn. des_ifs. steps. rewrite BDOOR. steps.
        des_ifs.
        { steps. econs; ss; et. rr. uipropall; ss. rewrite Any.upcast_downcast in *. clarify.
          rewrite insert_delete. rewrite insert_id; ss. sym. eapply Any.downcast_upcast; ss.
        }
        steps. gstep; econs; ss; et.
        { econs; ss; et. rr. uipropall; ss. rewrite Any.upcast_downcast in *. clarify.
          f_equal. rewrite insert_delete; ss. }
        ii. exists 100. steps.
    }
    admit "ez; TODO: make something like trivial tactic".
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Theorem correct: ModPair.sim (NewStack2.Stack) (SMod.to_src NewStack1.SStack).
  Proof.
    econs; ss. ii. eapply sim_modsem; ss.
  Qed.

End SIMMOD.
