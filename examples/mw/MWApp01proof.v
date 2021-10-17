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
  Context `{@GRA.inG AppRA.t Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    (* @mk_wf *)
    (*   _ *)
    (*   unit *)
    (*   (fun _ _ st_tgt => ((OwnM(AppInitX) ∧ ⌜st_tgt = false↑⌝) ∨ (OwnM(AppRunX) ∧ ⌜st_tgt = true↑⌝))%I) *)

    fun (_: unit) '(mpr_src, mpr_tgt) => (mpr_src = (InitX)↑ ∧ mpr_tgt = false↑) ∨
                                         (mpr_src = (RunX)↑ ∧ mpr_tgt = true↑)
  .

  Theorem correct: refines2 [MWApp0.App] [MWApp1.App].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { ss. }
    { esplits. econs; ss. }

    econs; ss.
    { init. steps. unfold initF, MWApp0.initF, ASSUME, GUARANTEE. steps.
      rr in WF. des; clarify; rewrite Any.upcast_downcast in *; clarify.
      2: { steps. des; clarify. ur in _ASSUME0. des_ifs. }
      steps. des; clarify. unfold ccallU. steps. force_l. exists (InitX, AppRA.unit, Init).
      steps. force_l; ss. steps. force_l; ss.
      { ur; ss. }
      steps. des; clarify; rewrite Any.upcast_downcast in *; clarify.
      2: { steps. des; clarify. ur in _ASSUME2. des_ifs. }
      steps. force_l. exists (RunX, Run, AppRA.unit). steps. force_l; ss. steps. des; clarify.
      assert(x = AppRA.unit). { ur in _ASSUME2. des_ifs. } subst.
      force_l; ss.
      { ur; ss. }
      steps. rr. esplits; et. rr. right; ss.
    }
    econs; ss.
    { init. steps. unfold runF, MWApp0.runF, ASSUME, GUARANTEE. steps.
      rr in WF. des; clarify; rewrite Any.upcast_downcast in *; clarify.
      1: { steps. des; clarify. ur in _ASSUME0. des_ifs. }
      steps. des; clarify. unfold ccallU. steps. force_l. exists (RunX, AppRA.unit, Run).
      steps. force_l; ss. steps. force_l; ss.
      { ur; ss. }
      steps. des; clarify; rewrite Any.upcast_downcast in *; clarify.
      1: { steps. des; clarify. ur in _ASSUME2. des_ifs. }
      steps. des; clarify. force_l. exists (RunX, Run, AppRA.unit). steps. force_l; ss. steps.
      assert(x = AppRA.unit). { ur in _ASSUME2. des_ifs. } subst.
      force_l; ss. steps. rr. esplits; et. rr. right; ss.
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
