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

Require Import HTactics ProofMode.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG AppRA Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ _ st_tgt => ((OwnM(AppInitX) ∧ ⌜st_tgt = false↑⌝) ∨ (OwnM(AppRunX) ∧ ⌜st_tgt = true↑⌝))%I)
  .

  Theorem correct: refines2 [MWApp0.App] [MWApp1.App].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { ss. }
    { esplits. econs; ss. eapply to_semantic. iIntros "H". iLeft. iSplits; ss. }

    econs; ss.
    { init. harg. mDesAll. des; clarify. unfold initF, ccallU. steps.
      mDesOr "INV"; mDesAll; des; clarify.
      2: { mAssertPure False; ss. iCombine "INV A" as "A". iOwnWf "A" as WF0. admit "ez". }
      steps. rewrite Any.upcast_downcast in *. clarify. steps.
      hcall _ _ _ with "INV"; auto.
      { esplits; ss. }
      steps. mDesAll; clarify. mDesOr "INV1"; mDesAll; clarify.
      2: { mAssertPure False; ss. iCombine "INV1 A" as "A". iOwnWf "A" as WF0. admit "ez". }
      rewrite _UNWRAPU. steps.
      mAssert _ with "*".
      { iCombine "A" "INV1" as "A". iApply (OwnM_Upd with "A").
        instantiate (1:=AppRun ⋅ AppRunX). admit "ez". }
      hret _; ss.
      { iMod "A1". iDestruct "A1" as "[A B]". iFrame. iSplits; ss; et. }
    }
    econs; ss.
    { init. harg. mDesAll. des; clarify. unfold runF, ccallU. steps.
      mDesOr "INV"; mDesAll; des; clarify.
      1: { mAssertPure False; ss. iCombine "INV A" as "A". iOwnWf "A" as WF0. admit "ez". }
      steps. rewrite Any.upcast_downcast in *. clarify. steps.
      hcall _ _ _ with "INV"; auto.
      { esplits; ss. }
      steps. mDesAll; clarify. mDesOr "INV1"; mDesAll; clarify.
      1: { mAssertPure False; ss. iCombine "INV1 A" as "A". iOwnWf "A" as WF0. admit "ez". }
      rewrite _UNWRAPU. steps.
      hret _; ss.
      { iFrame. iSplits; ss; et. }
    }
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
