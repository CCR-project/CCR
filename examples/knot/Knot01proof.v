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
  Context `{@GRA.inG knotRA Σ}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).

  Variable RecStb: SkEnv.t -> list (gname * fspec).
  Variable FunStb: SkEnv.t -> list (gname * fspec).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Let wf (skenv: SkEnv.t): W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ)(f': option (nat -> nat)),
        (<<SRC: mrps_src0 = (mr, tt↑)>>) /\
        (<<TGT: mrps_tgt0 = (ε, tt↑)>>) /\
        (<<SEP: iHyp ((Own (GRA.embed (knot_frag f')))
                      ∨
                      ((Own (GRA.embed (knot_full f')))
                         **
                         (Exists fb',
                          (Own (knot_var skenv fb'))
                            **
                            (⌜forall f (EQ: f' = Some f),
                                  exists fb fn,
                                    (<<BLK: fb' = Vptr fb 0>>) /\
                                    (<<FN: skenv.(SkEnv.blk2id) fb = Some fn>>) /\
                                    (<<FIND: List.find (fun '(_fn, _) => dec fn _fn) (FunStb skenv) = Some (fn, fun_gen RecStb skenv f)>>)⌝)))) mr>>).

        (<<TGT: mrps_tgt0 = (ε, fb'↑)>>) /\
        (<<SIM: (iHyp (Own (GRA.embed (knot_full f'))) mr)>>) /\
        (<<SOME: forall f (FUN: f' = Some f),
            exists fb,
              (<<BLK: fb' = Some fb>>) /\
              (<<FN: fb_has_spec skenv (FunStb skenv) fb (fun_gen RecStb skenv f)>>)>>)
  .

  Hypothesis RecStb_incl: forall skenv,
      stb_incl KnotRecStb (RecStb skenv).

  Hypothesis FunStb_incl: forall skenv,
      stb_incl (FunStb skenv) (GlobalStb skenv).

  Variable MemStb_incl
    :
      forall skenv fn fsp
             (SPECS: List.find (fun '(_fn, _) => dec fn _fn) MemStb = Some fsp),
        List.find (fun '(_fn, _) => dec fn _fn) (GlobalStb skenv) = Some fsp.

  (* AUX END -------------------------------------------- *)


  Theorem correct: ModPair.sim (Knot1.Knot RecStb FunStb GlobalStb) Knot0.Knot.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf (Sk.load_skenv sk)); et; ss.
    2: {
      eexists. exists None. esplits; ss. right.
      exists (GRA.embed (knot_full None)), (knot_var sk Vundef). splits; ss.
      { apply URA.add_comm. }
      { exists ε. rewrite URA.unit_id. ss. }
      { exists Vundef. exists (knot_var sk Vundef), (@URA.unit Σ). splits; ss.
        { rewrite URA.unit_id. ss. }
        { exists ε. rewrite URA.unit_id. ss. }
      }
    }
    hexploit (SKINCL "rec"); ss; eauto. intros [blk0 FIND0].
    hexploit (SKINCL "_f"); ss; eauto. intros [blk1 FIND1].
    econs; ss; [|econs; ss].
    { init. unfold recF, ccall. harg_tac. iRefresh.
      destruct x as [f n]. ss. des. subst.
      iRefresh. iDestruct PRE. iPure A. des; clarify.
      eapply Any.upcast_inj in A. des; clarify. steps.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify. astart 1.
      assert (f' = Some f); subst.
      { hexploit knot_ra_merge; et. intro T. iSpecialize T SIM. iSpecialize T PRE. iPure T. auto. }
      hexploit SOME; eauto. clear SOME. i. des. clarify. steps.
      rewrite Any.upcast_downcast. ss. steps.
      dup FN. inv FN. rewrite FBLOCK. steps.
      hexploit (SKINCL "rec"); ss; eauto. i. des. rewrite H0. ss. steps.
      inv SPEC. exploit FunStb_incl; et. i.
      acatch.
      { eapply x1. }
      hcall_tac_weaken (fun_gen RecStb skenv f) n (ord_pure (2 * n)) SIM (@URA.unit Σ) PRE.
      { et. }
      { ss. splits; ss. iRefresh. iSplitR PRE; ss.
        red. red. esplits; eauto. econs; eauto.
        { eapply SKWF. eauto. }
        econs.
        { eapply RecStb_incl. des_ifs. }
        { refl. }
      }
      { splits; ss. eauto with ord_step. }
      { ss. esplits; eauto. i. clarify. esplits; eauto. }
      des. clarify. iRefresh. iDestruct POST. iPure POST.
      eapply Any.upcast_inj in POST. des; clarify.
      steps. rewrite Any.upcast_downcast in _UNWRAPN. clarify.
      astop. force_l. eexists.
      hret_tac SEP A0; ss.
      { split; ss. iRefresh. iSplitL A0; ss. }
      { esplits; eauto. }
    }
    { init. unfold knotF, ccall. harg_tac.
      ss. des. subst.
      iRefresh. iDestruct PRE. iPure PRE. des; clarify.
      iDestruct A. eapply Any.upcast_inj in PRE. des; clarify. steps.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify. iDestruct SEP.
      { iExploitP (@knot_frag_unique _ _ f' x2); ss. }
      iDestruct SEP. astart 1.
      iMerge SEP A. rewrite <- own_sep in SEP.
      eapply own_upd in SEP; cycle 1; [|rewrite intro_iHyp in SEP;iUpdate SEP].
      { rewrite GRA.embed_add. eapply GRA.embed_updatable.
        instantiate (1:= knot_full (Some x) ⋅ knot_frag (Some x)).
        eapply Auth.auth_update. rr. ii. des; ss. ur in FRAME. ur. destruct ctx; ss; clarify.
      }
      rewrite <- GRA.embed_add in SIM. rewrite own_sep in SIM. iDestruct SIM.
      force_l. eexists.
      hret_tac SIM A; ss.
      { esplits; eauto. iRefresh. iSplitR A; eauto. red. red. esplits; eauto.
        econs; eauto.
        { eapply SKWF; eauto. }
        econs.
        { eapply RecStb_incl; eauto. ss. }
        { refl. }
      }
      { esplits; eauto. i. clarify. esplits; eauto. }
    }
  Qed.

End SIMMODSEM.
