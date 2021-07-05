Require Import HoareDef SimModSem.
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
(* Require Import TODOYJ. *)
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Require Import NewClient0 NewClientImp.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.

  Import ImpNotations.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Let wf: unit -> W -> Prop :=
    fun _ '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = tt↑>>) /\
      (<<TGT: mrps_tgt0 = tt↑>>)
  .

  Theorem correct:
    forall ge, ModSemPair.sim NewClient0.ClientSem (NewClientImp.ClientSem ge).
  Proof.
    Local Transparent syscalls.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss.
    { init.
      unfold getintF, getint.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n. solve_NoDup. }
      imp_steps.
      gstep. econs; ss. i. exists 100. imp_steps.
      red. esplits; et.
    }
    econs; ss.
    { init.
      steps.
      unfold putintF, putint.
      steps.
      rewrite unfold_eval_imp. steps.
      destruct (intrange_64 z) eqn:WFZ.
      2:{ steps. }
      des_ifs.
      2:{ exfalso; apply n. solve_NoDup. }
      imp_steps.
      unfold unint in *. clarify; ss. imp_steps.
      gstep. econs; ss. i. exists 100. imp_steps.
      red. esplits; et.
    }
    Local Opaque syscalls.
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
