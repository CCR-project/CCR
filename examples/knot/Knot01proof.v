Require Import HoareDef KnotHeader Knot0 Knot1 SimModSemL SimModSem.
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
            exists fb fn,
              (<<BLK: fb' = Some fb>>) /\
              (<<FN: skenv.(SkEnv.blk2id) fb = Some fn>>) /\
              (<<FIND: List.find (fun '(_fn, _) => dec fn _fn) (FunStb skenv) = Some (fn, mk_fspec (fun_gen RecStb skenv f))>>)>>)
  .

  Variable RecStb_incl
    :
      forall skenv fn fsp
             (SPECS: List.find (fun '(_fn, _) => dec fn _fn) KnotRecStb = Some fsp),
        List.find (fun '(_fn, _) => dec fn _fn) (RecStb skenv) = Some fsp.

  Variable FunStb_incl
    :
      forall skenv fn fsp
             (SPECS: List.find (fun '(_fn, _) => dec fn _fn) (FunStb skenv) = Some fsp),
        List.find (fun '(_fn, _) => dec fn _fn) (GlobalStb skenv) = Some fsp.

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
      rewrite Any.upcast_downcast. ss. steps. rewrite FN. ss. steps.
      hexploit (SKINCL "rec"); ss; eauto. i. des. rewrite H0. ss. steps.
      acall_tac_weaken (fun_gen RecStb skenv f) n (ord_pure (2 * n)) SIM (@URA.unit Σ) PRE.
      { eapply FunStb_incl. eapply FIND. }
      { refl. }
      { ss. splits; ss. iRefresh. iSplitR PRE; ss.
        red. red. esplits; eauto.
        { eapply SKWF. eauto. }
        { eapply RecStb_incl. des_ifs. }
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
      rewrite <- GRA.embed_add in SEP. rewrite own_sep in SEP. iDestruct SEP.
      steps. rewrite FIND1. steps.
      iDestruct A0. iDestruct A0. iPure A1.
      acall_tac (blk1, 0%Z, Vptr fb 0) (ord_pure 0) A SEP A0; ss.
      { eapply MemStb_incl. stb_tac. ss. }
      { splits; ss. iRefresh. iExists x5. iSplitL A0; ss.
        iSplitR A0; ss. unfold knot_var in *. rewrite FIND1 in *. iApply A0. }
      { splits; ss. eauto with ord_step. }
      { esplits; eauto. iLeft. iApply A. }
      steps. ss. des; clarify.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify. iDestruct SEP0; cycle 1.
      { iDestruct SEP0. iExploitP (@knot_full_unique _ _ f'0 (Some x)); ss. }
      iExploitP (@knot_ra_merge _ _ (Some x) f'0). i. subst.
      astop. rewrite FIND0. steps. force_l. eexists.
      iMerge POST SEP. hret_tac POST SEP0; ss.
      { esplits; eauto. iRefresh. iSplitR SEP0; ss. red. red. esplits; eauto.
        { eapply SKWF; eauto. }
        { eapply RecStb_incl; eauto. }
      }
      { iDestruct POST. esplits; eauto. iRight. iSplitL A; ss.
        { iApply A. }
        { iExists (Vptr fb 0). iSplitL POST.
          { unfold knot_var. rewrite FIND1. iApply POST. }
          { red. red. i. clarify. esplits; eauto. }
        }
      }
    }
  Qed.

End SIMMODSEM.
