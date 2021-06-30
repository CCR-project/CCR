Require Import HoareDef SimModSem.
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
Require Import Mem1 MemOpen STB.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Require Import NewStack0 NewStackImp.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Let wf: unit -> W -> Prop :=
    fun _ '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = (ε, tt↑)>>) /\
      (<<TGT: mrps_tgt0 = (ε, tt↑)>>)
  .

  Theorem correct:
    forall ge, ModSemPair.sim NewStack0.StackSem (NewStackImp.StackSem ge).
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss.
    - init.
      unfold newF.
      unfold new.
      steps.
      rewrite unfold_eval_imp.
      steps.
      force_r.
      solve_NoDup.
      imp_steps.
      force_r.
      ss.
      imp_steps.
      unfold ccall.
      steps.
      gstep. econs; ss. i. exists 100.
      imp_steps.
      force_r.
      (* Unshelve. all: ss. *)
  Admitted.

End SIMMODSEM.
