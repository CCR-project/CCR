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
        (<<SEP: iHyp ((Own (GRA.embed (knot_full f')))
                        **
                        ((Own (GRA.embed (knot_frag f')))
                         ∨
                         (Forall f,
                          (⌜f' = Some f⌝)
                            -*
                            Exists fb',
                          (⌜exists fb fn,
                                (<<BLK: fb' = Vptr fb 0>>) /\
                                (<<FN: skenv.(SkEnv.blk2id) fb = Some fn>>) /\
                                (<<FIND: List.find (fun '(_fn, _) => dec fn _fn) (FunStb skenv) = Some (fn, fun_gen RecStb skenv f)>>)⌝) ** (Own (knot_var skenv fb'))))) mr>>).

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


  (* AUX -------------------------------------------- *)
  Lemma unit_id_ b (EQ: b = @URA.unit Σ): forall a, a ⋅ b = a.
  Proof.
    subst. apply URA.unit_id.
  Qed.

  Ltac set_just name X :=
    let H := fresh "_tmp" in
    generalize I; intros H; set (name := X) in H; clear H.

  Ltac iImpure H :=
    let name := fresh "my_r" in
    set_just name (@URA.unit Σ);
    specialize (H name URA.wf_unit I); rewrite intro_iHyp in H;
    on_gwf
      ltac:(fun GWF =>
              rewrite <- (@unit_id_ name eq_refl) in GWF; clearbody name).

  Lemma pure_intro a (P: Prop):
    P -> ⌜P⌝ a.
  Proof.
    ss.
  Qed.

  Ltac iUnpure H :=
    let name := fresh "my_r" in
    set_just name (@URA.unit Σ);
    apply (@pure_intro name) in H; rewrite intro_iHyp in H;
    on_gwf
      ltac:(fun GWF =>
              rewrite <- (@unit_id_ name eq_refl) in GWF; clearbody name).

  Ltac iLeft := left; iRefresh.
  Ltac iRight := right; iRefresh.

  Definition EMP: iHyp (⌜ True ⌝) (@URA.unit Σ). ss. Qed.

  (* AUX END -------------------------------------------- *)


  Theorem correct: ModPair.sim (Knot1.Knot RecStb FunStb GlobalStb) Knot0.Knot.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf (Sk.load_skenv sk)); et; ss.
    2: {
      eexists. exists None. esplits; ss.
      exists (GRA.embed (knot_full None)), (knot_var sk Vundef). splits; ss.
      { apply URA.add_comm. }
      { exists ε. rewrite URA.unit_id. ss. }
      { right. ii. ss. }
    }
    hexploit (SKINCL "rec"); ss; eauto. intros [blk0 FIND0].
    hexploit (SKINCL "_f"); ss; eauto. intros [blk1 FIND1].
    econs; ss; [|econs; ss].
    { init. unfold recF, ccall. harg_tac. iRefresh.
      destruct x as [f n]. ss. des. subst.
      iRefresh. iDestruct PRE. iPure A. des; clarify.
      iDestruct SEP. iDestruct A0.
      { hexploit knot_frag_unique; et. intro T.
        iImpure T. iSpecialize T A0. iSpecialize T PRE. ss. }
      rewrite FIND1. eapply Any.upcast_inj in A. des; clarify. steps.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify. astart 1.
      assert (f' = Some f); subst.
      { hexploit knot_ra_merge; et. intro T.
        iImpure T. iSpecialize T SEP. iSpecialize T PRE. iPure T. auto. }
      specialize (A0 f). iRefresh.
      assert (TMP: Some f = Some f); auto.
      iUnpure TMP. iRefresh. iSpecialize A0 TMP.
      iDestruct A0. iDestruct A0. iPure A0. des. clarify.
      steps. iMerge PRE SEP.
      acall_tac (blk1, 0%Z, Vptr fb 0) (ord_pure 1) PRE (@URA.unit Σ) A.
      { eapply MemStb_incl. ss. stb_tac. ss. }
      { splits; ss. iRefresh. iSplitL A; ss.
        iSplitR A; ss. unfold knot_var in *. rewrite FIND1 in *. iApply A. }
      { splits; ss. admit "fix mem". }
      { unfold wf. iDestruct PRE. esplits; eauto. iRefresh.
        iSplitL A0.
        { iApply A0. }
        { iLeft. iApply PRE. }
      }
      iDestruct SEP.
      steps.

left. iLeft.


        iSplitR



 eauto with ord_step.
iApply A.

red. red. esplits; eauto.
        { eapply SKWF. eauto. }
        { eapply RecStb_incl. des_ifs. }
      }

Ltac hcall_tac x o MR_SRC1 FR_SRC1 RARG_SRC :=


      acatch.

      rewrite Any.upcast_downcast. ss. steps. rewrite FN. ss. steps.
      hexploit (SKINCL "rec"); ss; eauto. i. des. rewrite H0. ss. steps.
      acall_tac n (ord_pure (2 * n)) SIM (@URA.unit Σ) PRE; ss.
      { eapply FunStb_incl. eauto. }
      { splits; ss. iRefresh. iSplitR PRE; ss.
        red. red. esplits; eauto.
        { eapply SKWF. eauto. }
        { eapply RecStb_incl. des_ifs. }
      }
      { splits; ss. eauto with ord_step. }
      { esplits; eauto. i. clarify. esplits; eauto. }
      ss. des. clarify. iRefresh. iDestruct POST. iPure POST.
      eapply Any.upcast_inj in POST. des; clarify.
      steps. rewrite Any.upcast_downcast in _UNWRAPN. clarify.
      astop. force_l. eexists.
      hret_tac SIM0 A; ss.
      { split; ss. iRefresh. iSplitL A; ss. }
      { esplits; eauto. }
    }
    { init. unfold knotF, ccall. harg_tac.
      ss. des. subst.
      iRefresh. iDestruct PRE. iPure PRE. des; clarify.
      iDestruct A. eapply Any.upcast_inj in PRE. des; clarify. steps.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify. astart 0. astop.
      steps. hexploit (SKINCL "rec"); ss; eauto. i. des. rewrite H0. ss. steps.
      iRefresh. iMerge SIM A.

      rewrite <- own_sep in SIM.
      eapply own_upd in SIM; cycle 1; [|rewrite intro_iHyp in SIM;iUpdate SIM].
      { rewrite GRA.embed_add. eapply GRA.embed_updatable.
        instantiate (1:= knot_full (Some x) ⋅ knot_frag (Some x)).
        eapply Auth.auth_update. rr. ii. des; ss. ur in FRAME. ur. destruct ctx; ss; clarify.
      }
      rewrite <- GRA.embed_add in SIM. rewrite own_sep in SIM. iDestruct SIM.
      force_l. eexists.
      hret_tac SIM A; ss.
      { esplits; eauto. iRefresh. iSplitR A; eauto. red. red. esplits; eauto.
        { eapply SKWF; eauto. }
        { eapply RecStb_incl; eauto. }
      }
      { esplits; eauto. i. clarify. esplits; eauto. }
    }
  Qed.

End SIMMODSEM.
