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

Require Import Knot0 KnotImp.

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
    ModPair.sim Knot0.Knot KnotImp.Knot.
  Proof.
    econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss.
    { init.
      unfold recF, rec.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n0. solve_NoDup. }
      imp_steps.
      rewrite _UNWRAPU1.
      unfold ccallU. imp_steps.
      gstep. econs; ss. i. exists 100. imp_steps.
      rewrite _UNWRAPU5. imp_steps.
      unfold unblk in *. des_ifs_safe; ss; clarify.
      imp_steps.
      unfold unint in *. ss; clarify. des_ifs; clarify.
      gstep. econs; ss. i. exists 100. imp_steps.
      red. esplits; et.
    }
    econs; ss.
    { init.
      steps.
      unfold knotF, knot.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n1. solve_NoDup. }
      imp_steps.
      unfold unblk in *. des_ifs.
      rewrite _UNWRAPU1. ss.
      unfold ccallU. imp_steps.
      gstep. econs; ss. i. exists 100. imp_steps.
      rewrite _UNWRAPU2. ss.
      imp_steps.
      red. esplits; et.
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
