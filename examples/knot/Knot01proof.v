Require Import HoareDef STB KnotHeader Knot0 Knot1 SimModSemL SimModSem.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import Mem1.
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

Require Import HTactics Logic YPM TODOYJ.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.





(* copied from BW01proof *)
Section AUX.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG knotRA Σ}.
  Lemma knot_ra_merge
        f0 f1
    :
      ⌞(Own (GRA.embed (knot_full f0)) -* Own (GRA.embed (knot_frag f1)) -* (⌜f1 = f0⌝))⌟
  .
  Proof.
    iIntro; clear A.
    do 2 iIntro.
    {
      iMerge A A0. rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. eapply GRA.embed_wf in WF. des. eapply Auth.auth_included in WF. des.
      eapply Excl.extends in WF; ss.
      - des; clarify.
      - ur; ss.
    }
  Qed.

  Lemma knot_frag_unique
        f0 f1
    :
      ⌞(Own (GRA.embed (knot_frag f0)) -* Own (GRA.embed (knot_frag f1)) -* (⌜False⌝))⌟
  .
  Proof.
    iIntro; clear A.
    do 2 iIntro.
    {
      iMerge A A0. rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. eapply GRA.embed_wf in WF. des.
      ur in WF. ur in WF. ss.
    }
  Qed.

  Lemma knot_full_unique
        f0 f1
    :
      ⌞(Own (GRA.embed (knot_full f0)) -* Own (GRA.embed (knot_full f1)) -* (⌜False⌝))⌟
  .
  Proof.
    iIntro; clear A.
    do 2 iIntro.
    {
      iMerge A A0. rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. eapply GRA.embed_wf in WF. des.
      ur in WF. ur in WF. ss.
    }
  Qed.
End AUX.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).

  Variable RecStb: SkEnv.t -> list (gname * fspec).
  Variable FunStb: SkEnv.t -> list (gname * fspec).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Let wf (skenv: SkEnv.t): W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ),
        (<<SRC: mrps_src0 = (mr, tt↑)>>) /\
        (<<TGT: mrps_tgt0 = (ε, tt↑)>>) /\
        (<<SEP: (inv_closed
                 ∨
                 ((inv_open)
                    **
                    (Exists (f': option (nat -> nat)) (fb': val),
                     (⌜forall f (EQ: f' = Some f),
                           exists fb,
                             (<<BLK: fb' = Vptr fb 0>>) /\
                             (<<FN: fb_has_spec skenv (FunStb skenv) fb (fun_gen RecStb skenv f)>>)⌝)
                       ** (Own (GRA.embed (knot_full f')))
                       ** (Own (knot_var skenv fb'))))) mr>>).

  Hypothesis RecStb_incl: forall skenv,
      stb_incl KnotRecStb (RecStb skenv).

  Hypothesis FunStb_incl: forall skenv,
      stb_incl (FunStb skenv) (GlobalStb skenv).

  Variable MemStb_incl: forall skenv,
      stb_incl MemStb (GlobalStb skenv).

  Theorem correct: ModPair.sim (Knot1.Knot RecStb FunStb GlobalStb) Knot0.Knot.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf (Sk.load_skenv sk)); et; ss.
    2: {
      eexists. esplits; ss. right.
      exists (GRA.embed inv_black), (knot_var sk Vundef ⋅ GRA.embed (knot_full None)).
      splits; ss.
      { r_solve. }
      { exists ε. r_solve. }
      exists None, Vundef.
      exists (GRA.embed (knot_full None)), (knot_var sk Vundef). splits; ss.
      { r_solve. }
      2: { exists ε. r_solve. }
      exists ε, (GRA.embed (knot_full None)). splits; ss.
      { r_solve. }
      { exists ε. r_solve. }
    }
    hexploit (SKINCL "rec"); ss; eauto. intros [blk0 FIND0].
    hexploit (SKINCL "_f"); ss; eauto. intros [blk1 FIND1].
    econs; ss; [|econs; ss].
    { init. unfold recF, ccall. harg_tac. iRefresh.
      destruct x as [f n]. ss. des. subst.
      iRefresh. iDestruct PRE. iDestruct PRE. iPure PRE. des; clarify.
      eapply Any.upcast_inj in PRE. des; clarify. steps.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify. astart 2.
      iDestruct SEP.
      { inv_clear. }
      iDestruct SEP. iDestruct A1. iDestruct A1. iDestruct A1. iDestruct A1. iPure A1.
      iExploitP (@knot_ra_merge _ _ x4 (Some f)). i. subst.
      hexploit A1; eauto. clear A1. i. des. clarify. steps.
      rewrite FIND1. steps.
      acatch.
      { eapply MemStb_incl. stb_tac. ss. }
      iMerge A3 A0. iMerge A3 SEP.
      hcall_tac (blk1, 0%Z, Vptr fb 0) (ord_pure 0) A A3 A2.
      { ss. splits; ss. iRefresh. iSplitL A2; ss. iSplitR A2; ss.
        unfold knot_var in *. rewrite FIND1 in *. ss. }
      { splits; ss. eauto with ord_step. }
      { red. eexists. esplits; eauto. left. ss. }
      steps. des. iRefresh. iDestruct POST. iPure A.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify.
      eapply Any.upcast_inj in A. des; clarify. steps.
      dup FN. inv FN. inv SPEC. rewrite FBLOCK. steps.
      rewrite FIND0. steps. acatch.
      { eapply FunStb_incl. eapply FIND. }
      iDestruct A3. iDestruct A3. iDestruct SEP.
      2:{ iDestruct SEP. inv_clear. }
      iMerge A0 SEP. iMerge A POST. iMerge A A3.
      hcall_tac_weaken (fun_gen RecStb sk f) n (ord_pure (2 * n)) A (@URA.unit Σ) A0; ss.
      { split; auto. iRefresh. iDestruct A0. iSplitR A; ss. iSplitR A0; ss.
        red. red. esplits; eauto. econs.
        { eapply SKWF. eauto. }
        econs.
        { eapply RecStb_incl. des_ifs. }
        { refl. }
      }
      { splits; ss. eauto with ord_step. }
      { esplits; eauto. iRight.
        iDestruct A. iDestruct A. iSplitL A; ss.
        iExists (Some f). iExists __. iSplitR A1.
        { iSplitR A0; ss.
          red. red. i. clarify. esplits; eauto. }
        { unfold knot_var. rewrite FIND1. iApply A1. }
      }
      steps. des. clarify. iRefresh.
      iDestruct POST. iDestruct POST. iPure POST.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify.
      eapply Any.upcast_inj in POST. des; clarify. iMerge A0 A.
      astop. force_l. eexists.
      hret_tac SEP A0.
      { split; ss. iRefresh. iDestruct A0. iSplitR A; ss. iSplitR A0; ss. }
      { red. esplits; eauto. }
    }
    { init. unfold knotF, ccall. harg_tac.
      ss. des. subst.
      iRefresh. iDestruct PRE. iDestruct PRE. iPure PRE. des; clarify.
      eapply Any.upcast_inj in PRE. des; clarify.
      iDestruct A0. iDestruct SEP.
      { inv_clear. }
      rewrite Any.upcast_downcast. steps.
      iDestruct SEP. iDestruct A1. iDestruct A1.
      iDestruct A1. iDestruct A1.
      unfold knot_var in *. rewrite FIND1 in *. steps.
      astart 1. acatch.
      { eapply MemStb_incl. stb_tac. ss. }
      iMerge A3 A0. iMerge A3 SEP.
      hcall_tac (blk1, 0%Z, Vptr fb 0) (ord_pure 0) A A3 A2.
      { ss. splits; ss. iRefresh. iExists __. iSplitL A2; ss.
        iSplitR A2; ss. iApply A2. }
      { splits; ss. eauto with ord_step. }
      { red. esplits; eauto. left. ss. }
      steps. astop. des; clarify.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify.
      iDestruct A3. iDestruct A3. iDestruct SEP.
      2: { iDestruct SEP. inv_clear. }
      iExploitP (@knot_ra_merge _ _ x6 x0). i. subst.
      iMerge A3 A0. rewrite <- own_sep in A3.
      eapply own_upd in A3; cycle 1; [|rewrite intro_iHyp in A3;iUpdate A3].
      { rewrite GRA.embed_add. eapply GRA.embed_updatable.
        instantiate (1:= knot_full (Some x) ⋅ knot_frag (Some x)).
        eapply Auth.auth_update. rr. ii. des; ss.
        ur in FRAME. ur. destruct ctx; ss; clarify.
      }
      replace tmp0 with (x12 ⋅ x13); [|admit "iMerge bug"].
      rewrite <- GRA.embed_add in A3. rewrite own_sep in A3. iDestruct A3.
      steps. rewrite FIND0. steps.
      iMerge POST A. iMerge POST A3. iMerge SEP A0.
      force_l. eexists.
      hret_tac POST SEP.
      { split; eauto. iRefresh. iDestruct SEP. iSplitR SEP; ss.
        iSplitR A; ss.
        { red. red. esplits; eauto. econs.
          { eapply SKWF. eauto. }
          econs.
          { eapply RecStb_incl. ss. }
          { refl. }
        }
      }
      { red. esplits; eauto. iRight. iDestruct POST. iDestruct POST.
        iSplitL A0; ss. iExists (Some x). iExists __. iSplitR POST.
        { iSplitR A; ss. red. red. i. clarify. esplits; eauto. }
        { rewrite Heq. ss. }
      }
    }
  Qed.

End SIMMODSEM.
