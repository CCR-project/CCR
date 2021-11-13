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

Require Import HTactics2 ProofMode STB.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG AppRA.t Σ}.
  Context `{@GRA.inG mwRA Σ}.
  Context `{@GRA.inG spRA Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (* (fun _ _ mpr_tgt => (∃ (mr_tgt: AppRA), ⌜mpr_tgt = Any.pair tt↑ (GRA.embed mr_tgt)↑⌝ ** OwnM mr_tgt)%I) *)
      (* (fun _ _ mpr_tgt => (∃ (rm: AppRA.t), ⌜mpr_tgt = rm↑⌝ ** OwnM rm)%I) *)
      (fun _ _ _ => True%I)
  .

  Opaque AppRA.t. (****************** todo move to the root ******************)
  Opaque mwRA.
  Opaque Z.eq_dec Z.eqb.

  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk, stb_incl (to_stb MWStb) (global_stb sk).

  Theorem correct: refines2 [MWApp1.App] [MWApp2.App global_stb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits. econs; et. eapply to_semantic. iIntros "A". iFrame. }

    econs.
    {
      (*** init ***)
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)

      unfold initF, ccallU.
      harg. fold wf.
      mDesAll; des; clarify. steps.
      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      harg_tgt.
      { iFrame. iModIntro. iSplits; ss; et. xtra. }
      steps. stb_tac. clarify.
      hcall _ _.
      { instantiate (2:=(_,_,_)). cbn. iDes; des; clarify. iDestruct "FR" as "[A B]". iFrame.
        iModIntro. iSplits; ss; et. instantiate (1:=True%I); ss. }
      { i. iIntros "H". ss. }
      fold wf. mDesAll; des; clarify. steps.
      hpost_tgt.
      { iFrame. iModIntro. iSplits; ss; et. xtra. }
      steps. rewrite _UNWRAPU. steps.

      hret _; ss.
      { iDestruct "Q" as "[Q %]". subst. iDestruct "FR" as "[A B]". iFrame. iSplits; ss; et. }
      { iDestruct "Q" as "[Q %]". subst. fold wf in WF0. iPureIntro. r. esplits; et. }
    }

    econs.
    {
      (*** init ***)
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)

      unfold runF, ccallU.
      harg. fold wf.
      mDesAll; des; clarify. steps.
      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      harg_tgt.
      { iFrame. iModIntro. iSplits; ss; et. xtra. }
      steps. stb_tac. clarify.
      hcall _ _.
      { instantiate (2:=(_,_,_)). cbn. iDes; des; clarify. iDestruct "FR" as "[A B]". iFrame.
        iModIntro. iSplits; ss; et. instantiate (1:=True%I); ss. }
      { i. iIntros "H". ss. }
      fold wf. mDesAll; des; clarify. steps.
      hpost_tgt.
      { iFrame. iModIntro. iSplits; ss; et. xtra. }
      steps. force_r; ss. steps. rewrite _UNWRAPU. steps.

      hret _; ss.
      { iDestruct "Q" as "[Q %]". subst. iDestruct "FR" as "[A B]". iFrame. iSplits; ss; et. }
      { iDestruct "Q" as "[Q %]". subst. fold wf in WF0. iPureIntro. r. esplits; et. }
    }

    econs; ss.
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
