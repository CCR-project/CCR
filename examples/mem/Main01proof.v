Require Import Main0 Main1 HoareDef SimModSem.
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
Require Import HTactics Logic YPM.
Require Import Mem1.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Let wf: W -> Prop := top1.

  Theorem correct: ModSemPair.sim Main1.MainSem Main0.MainSem.
  Proof.
    econs; ss.
    econs; ss.
    { unfold mainF. init.
      harg_tac. iRefresh. iDestruct PRE; subst. unfold mainBody. steps. force_l; stb_tac; clarify. steps.
      Set Printing All.
      rewrite Any.upcast_downcast.
      steps. ss. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      iRefresh. iDestruct PRE. iPure PRE. subst. steps. rewrite Any.upcast_downcast. steps.
      hide_k.
      steps.
    }
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Let wf: W -> Prop := top1.

  Theorem correct: ModPair.sim Main1.Main Main0.Main.
  Proof.
  Qed.

End SIMMOD.
