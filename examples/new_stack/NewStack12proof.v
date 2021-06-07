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
           (fun _ _ _ => ⌜True⌝%I)
           (fun _ _ _ => ⌜True⌝%I)
  .

  Theorem sim_modsem: ModSemPair.sim (NewStack2.StackSem) (KModSem.to_src NewStack1.KStackSem).
  Proof.
    econstructor 1 with (wf:=wf); ss; et; swap 2 3.
    { econs; ss.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iPureIntro. ss.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iPureIntro. ss.
    }
    econs; ss.
    { unfold NewStack1.new_body, NewStack2.new_body, KModSem.fun_to_src,KModSem.body_to_src, cfun. init. steps.
      admit "mid - somehow".
    }
    admit "mid - somehow".
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Theorem correct: ModPair.sim (NewStack2.Stack) (KMod.to_src NewStack1.KStack).
  Proof.
    econs; ss.
    { ii. eapply adequacy_lift. eapply sim_modsem; ss. }
    ii; ss. repeat (Psimpl; econs; ss).
  Qed.

End SIMMOD.
