Require Import HoareDef MWHeader MWApp1 MWApp2 SimModSem.
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
  Context `{@GRA.inG mwRA Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (* (fun _ _ mpr_tgt => (∃ (mr_tgt: AppRA), ⌜mpr_tgt = Any.pair tt↑ (GRA.embed mr_tgt)↑⌝ ** OwnM mr_tgt)%I) *)
      (fun _ _ mpr_tgt => (∃ (rm: AppRA.t), ⌜mpr_tgt = rm↑⌝ ** OwnM rm)%I)
  .

  Opaque AppRA.t. (****************** todo move to the root ******************)
  Opaque mwRA.
  Opaque Z.eq_dec Z.eqb.

  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk, stb_incl (to_stb MWStb) (global_stb sk).

  Theorem correct: refines2 [MWApp1.App] [MWApp2.App global_stb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { ss. }
    (* { esplits. econs; ss. eapply to_semantic. iIntros "H". iSplits; ss. } *)
    { esplits. econs; ss. eapply to_semantic. iIntros "H". iSplits; ss. }

    econs; ss.
    { init. harg. mDesAll. des; clarify. rename x into mwf. rename a into _lower_layer_rm.
      steps. unfold initF, ASSUME, GUARANTEE. steps.
      force_r. exists Init. steps. force_r; ss. steps. force_r. eexists. steps. force_r; ss.
      { esplits; et. admit "ez". }
      steps. rename c0 into rm. rename c1 into ro. rename c into rf1.
      rewrite URA.unit_id in _GUARANTEE0.
      mCombine "A1" "A2". mEval ltac:(erewrite URA.add_comm; erewrite <- _GUARANTEE0) in "A1".
      unfold ccallU. steps. des. clear_tac. mDesOwn "A1" as "B" "C".
      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ (_, _, _) _ with "A B".
      { iModIntro. iDestruct "B" as "[B C]". iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      steps. mDesAll; clarify.
      rewrite _UNWRAPU. steps. force_r. exists ε. steps. force_r; ss. steps. force_r. rename a into rm0.
      eexists. steps. force_r; ss.
      { rewrite URA.unit_id. esplits; et. admit "ez". }
      steps. des; clarify.
      mAssert _ with "C A".
      { iCombine "A" "C" as "A". (* sym in _GUARANTEE. iRewrite _GUARANTEE in "A". *) iExact "A". }
      mEval ltac:(erewrite <- _GUARANTEE) in "A1".

      hret _; ss.
      { iModIntro. iDestruct "A1" as "[[A B] C]". iFrame. iSplitL "A"; et. }
    }

    econs; ss.
    { init. harg. mDesAll. des; clarify. rename x into mwf. rename a into _lower_layer_rm.
      steps. unfold runF, ASSUME, GUARANTEE. steps.
      force_r. exists Run. steps. force_r; ss. steps. force_r. eexists. steps. force_r; ss.
      { esplits; et. admit "ez". }
      steps. rename c0 into rm. rename c1 into ro. rename c into rf1.
      rewrite URA.unit_id in _GUARANTEE0.
      mCombine "A1" "A2". mEval ltac:(erewrite URA.add_comm; erewrite <- _GUARANTEE0) in "A1".
      unfold ccallU. steps. des. clear_tac. mDesOwn "A1" as "B" "C".
      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ (_, _, _) _ with "A B".
      { iModIntro. iDestruct "B" as "[B C]". iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      steps. mDesAll; clarify.
      rewrite _UNWRAPU. steps. rewrite Any.upcast_downcast in *. clarify. steps.
      force_r. exists ε. steps. force_r; ss. steps. force_r. rename a into rm0.
      eexists. steps. force_r; ss.
      { rewrite URA.unit_id. esplits; et. admit "ez". }
      steps. des; clarify.
      mAssert _ with "C A".
      { iCombine "A" "C" as "A". (* sym in _GUARANTEE. iRewrite _GUARANTEE in "A". *) iExact "A". }
      mEval ltac:(erewrite <- _GUARANTEE) in "A2".

      hret _; ss.
      { iModIntro. iDestruct "A2" as "[[A B] C]". iFrame. iSplitL "A"; et. }
    }
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
