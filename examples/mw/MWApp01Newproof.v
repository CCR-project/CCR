Require Import HoareDef MWHeader MWApp0 MWApp1New SimModSem.
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
    (* @mk_wf *)
    (*   _ *)
    (*   unit *)
    (*   (fun _ _ st_tgt => ((OwnM(AppInitX) ∧ ⌜st_tgt = false↑⌝) ∨ (OwnM(AppRunX) ∧ ⌜st_tgt = true↑⌝))%I) *)

    fun (_: unit) '(mpr_src, mpr_tgt) => (mpr_src = (AppInitX)↑ ∧ mpr_tgt = false↑) ∨
                                         (mpr_src = (AppRunX)↑ ∧ mpr_tgt = true↑)
  .

  Theorem correct: refines2 [MWApp0.App] [MWApp1New.App].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { ss. }
    { esplits. econs; ss. }

    econs; ss.
    { init. steps. unfold initF, MWApp0.initF, ASSUME, GUARANTEE. steps.
      rr in WF. des; clarify; rewrite Any.upcast_downcast in *; clarify.
      2: { steps. des; clarify. admit "ez". }
      steps. des; clarify. unfold ccallU. steps. force_l. exists (AppInitX, @URA.unit AppRA, AppInit).
      steps. force_l; ss. steps. force_l; ss.
      { admit "ez". }
      steps. des; clarify; rewrite Any.upcast_downcast in *; clarify.
      2: { steps. des; clarify. admit "ez". }
      steps. force_l. exists (AppRunX, AppRun, @URA.unit AppRA). steps. force_l; ss. steps. des; clarify.
      force_l; ss.
      { admit "ez". }
      steps. rr. esplits; et. rr. right; ss.
    }
    econs; ss.
    { init. steps. unfold runF, MWApp0.runF, ASSUME, GUARANTEE. steps.
      rr in WF. des; clarify; rewrite Any.upcast_downcast in *; clarify.
      1: { steps. des; clarify. admit "ez". }
      steps. des; clarify. unfold ccallU. steps. force_l. exists (AppRunX, @URA.unit AppRA, AppRun).
      steps. force_l; ss. steps. force_l; ss.
      { admit "ez". }
      steps. des; clarify; rewrite Any.upcast_downcast in *; clarify.
      1: { steps. des; clarify. admit "ez". }
      steps. des; clarify. force_l. exists (AppRunX, AppRun, @URA.unit AppRA). steps. force_l; ss. steps.
      force_l; ss.
      { admit "ez". }
      steps. rr. esplits; et. rr. right; ss.
    }
    (*   { left. ss. esplits; et. *)
    (*   des; clarify. *)
    (*   { rewrite Any.upcast_downcast in *. clarify. steps. *)
    (*   harg. mDesAll. des; clarify. unfold initF, ccallU. steps. *)
    (*   mDesOr "INV"; mDesAll; des; clarify. *)
    (*   2: { mAssertPure False; ss. iCombine "INV A" as "A". iOwnWf "A" as WF0. admit "ez". } *)
    (*   steps. rewrite Any.upcast_downcast in *. clarify. steps. *)
    (*   hcall _ _ _ with "INV"; auto. *)
    (*   { esplits; ss. } *)
    (*   steps. mDesAll; clarify. mDesOr "INV1"; mDesAll; clarify. *)
    (*   2: { mAssertPure False; ss. iCombine "INV1 A" as "A". iOwnWf "A" as WF0. admit "ez". } *)
    (*   rewrite _UNWRAPU. steps. *)
    (*   mAssert _ with "*". *)
    (*   { iCombine "A" "INV1" as "A". iApply (OwnM_Upd with "A"). *)
    (*     instantiate (1:=AppRun ⋅ AppRunX). admit "ez". } *)
    (*   hret _; ss. *)
    (*   { iMod "A1". iDestruct "A1" as "[A B]". iFrame. iSplits; ss; et. } *)
    (* } *)
    (* econs; ss. *)
    (* { init. harg. mDesAll. des; clarify. unfold runF, ccallU. steps. *)
    (*   mDesOr "INV"; mDesAll; des; clarify. *)
    (*   1: { mAssertPure False; ss. iCombine "INV A" as "A". iOwnWf "A" as WF0. admit "ez". } *)
    (*   steps. rewrite Any.upcast_downcast in *. clarify. steps. *)
    (*   hcall _ _ _ with "INV"; auto. *)
    (*   { esplits; ss. } *)
    (*   steps. mDesAll; clarify. mDesOr "INV1"; mDesAll; clarify. *)
    (*   1: { mAssertPure False; ss. iCombine "INV1 A" as "A". iOwnWf "A" as WF0. admit "ez". } *)
    (*   rewrite _UNWRAPU. steps. *)
    (*   hret _; ss. *)
    (*   { iFrame. iSplits; ss; et. } *)
    (* } *)
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
