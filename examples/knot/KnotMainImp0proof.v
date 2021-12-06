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

Require Import KnotMain0 KnotMainImp.

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
    refines2 [KnotMainImp.KnotMain] [KnotMain0.Main].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss.
    { init.
      unfold fibF, fib.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n0. solve_NoDup. }
      3:{ exfalso; apply n0. solve_NoDup. }
      - imp_steps.
        unfold unint in *. clarify.

        des_ifs; ss; clarify.
        2:{ lia. }
        imp_steps.
        red. esplits; et.
      - imp_steps.
        unfold unint in *. des_ifs; ss; clarify.
        { lia. }
        imp_steps.
        unfold ccallU. imp_steps.
        red. esplits; et.
    }
    econs; ss.
    { init.
      steps.
      unfold mainF, main.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n0. solve_NoDup. }
      imp_steps.
      rewrite _UNWRAPU0. unfold ccallU. imp_steps.
      red. esplits; et.
    }
    Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
