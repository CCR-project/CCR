Require Import HoareDef OpenDef STB RepeatImp Repeat0 SimModSem.
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

Require Import HTactics ProofMode Invariant.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Set Implicit Arguments.

Local Open Scope nat_scope.





Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop := fun (_: unit) _ => True.

  Theorem correct: refines2 [RepeatImp.Repeat] [Repeat0.Repeat].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits; et. ss. }
    econs; ss. init. steps.
    unfold RepeatImp.repeat, repeatF.
    rewrite unfold_eval_imp. imp_steps.
    unfold unint, unblk in *. des_ifs.
    2, 4: exfalso; eapply n0; solve_NoDup.
    { imp_steps. red. esplits; et. }
    { unfold ccallU. imp_steps. des_ifs.
      { exfalso. lia. }
      imp_steps. gstep. econs; et. i. exists 100.
      imp_steps. gstep. econs; et. i. exists 100.
      imp_steps. red. esplits; et.
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
