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

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    fun (_: unit) '(mp_src, mp_tgt) => mp_src = mp_tgt.

  Variable frds: list mname.

  Theorem sim_modsem: ModSemPair.sim (NewStack2.StackSem) (KModSem.transl_src frds NewStack1.KStackSem).
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    assert(BDOOR: (KModSem.interp_kCallE_src APCK) = Ret tt).
    { admit "mid - BDOOR". }
    econs; ss.
    { init. inv WF.
      unfold fun_to_src, body_to_src, KModSem.body_to_src, cfun, new_body, NewStack1.new_body.
      steps. rewrite my_if_same. steps.
      rewrite BDOOR. steps.
      force_l. esplits. steps. rewrite _UNWRAPN0. steps. rewrite _GUARANTEE. force_l; ss. steps.
      red. esplits; et. econs; ss; et. 
    }
    econs; ss.
    { init. inv WF.
      unfold fun_to_src, body_to_src, KModSem.body_to_src, cfun, pop_body, NewStack1.pop_body.
      steps. rewrite my_if_same. steps.
      rewrite BDOOR. steps. apply Any.downcast_upcast in _UNWRAPN0. des; subst. des_ifs; steps.
      { red. esplits; et. rewrite Any.upcast_downcast in *. clarify. 
        rewrite insert_delete; ss. rewrite insert_id; ss. }
      { red. esplits; et. rewrite Any.upcast_downcast in *. clarify. 
        rewrite insert_delete; ss. }
    }
    admit "ez".
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Variable frds: Sk.t -> list mname.

  Theorem correct: ModPair.sim (NewStack2.Stack) (KMod.transl_src frds NewStack1.KStack).
  Proof.
    econs; ss. ii. eapply sim_modsem; ss.
  Qed.

End SIMMOD.
