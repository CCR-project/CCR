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
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Require Import Echo0 EchoImp.

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
    refines2 [EchoImp.Echo] [Echo0.Echo].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss.
    { init.
      unfold echo_body, echo.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n. solve_NoDup. }
      unfold ccallU. imp_steps.
      red. esplits; et.
    }
    econs; ss.
    { init.
      unfold input_body, input.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n. solve_NoDup. }
      unfold ccallU. imp_steps.
      des. destruct v0; ss; clarify.
      des_ifs.
      - imp_steps. red. esplits; et. ss.
      - rewrite Z.eqb_eq in Heq. clarify.
      - imp_steps. red. esplits; et.
    }
    econs; ss.
    { init.
      unfold output_body, output.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n. solve_NoDup. }
      unfold ccallU. imp_steps.
      des. destruct v0; ss; clarify.
      des_ifs.
      - imp_steps. red. esplits; et. ss.
      - rewrite Z.eqb_eq in Heq. clarify.
      - imp_steps. red. esplits; et.
    }
    Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
