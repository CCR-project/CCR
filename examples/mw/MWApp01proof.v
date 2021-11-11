Require Import HoareDef MWHeader MWApp0 MWApp1 SimModSem.
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

Require Import HTactics ProofMode STB.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG AppRA.t Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ _ st_tgt => ((OwnM(Run) ∧ ⌜st_tgt = false↑⌝) ∨ (OwnM(Init) ∧ ⌜st_tgt = true↑⌝))%I)
  .

  Theorem correct: refines2 [MWApp0.App] [MWApp1.App].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { ss. }
    { esplits. econs; ss. eapply to_semantic. iIntros "H". iSplits; ss; et. }

    econs; ss.
    { init. harg. mDesAll; des; clarify. fold wf. steps. unfold initF, MWApp0.initF, ccallU. steps.
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { admit "ez". }
      rewrite Any.upcast_downcast in *. clarify. steps. force_l; stb_tac; ss; clarify. steps.

      hcall _ _ _ with "INV".
      { iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify.
      mDesOr "INV1"; mDesAll; des; clarify; cycle 1.
      { admit "ez". }
      steps. hret _; ss.
      { iModIntro. iFrame. iSplits; ss; et. }
    }
    econs; ss.
    { init. harg. mDesAll; des; clarify. fold wf. steps. unfold runF, MWApp0.runF, ccallU. steps.
      mDesOr "INV"; mDesAll; des; clarify.
      { admit "ez". }
      rewrite Any.upcast_downcast in *. clarify. steps. force_l; stb_tac; ss; clarify. steps.

      hcall _ _ _ with "INV".
      { iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify.
      mDesOr "INV1"; mDesAll; des; clarify.
      { admit "ez". }
      steps. force_r; ss. exists; ss. steps. unfold unint in *. des_ifs. steps.
      hret _; ss.
      { iModIntro. iFrame. iSplits; ss; et. }
    }
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
