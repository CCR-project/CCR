Require Import HoareDef KnotHeader Knot0 Knot1 SimModSemL SimModSem.
Require Import Coqlib.
Require Import Universe.
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
      iHyp (Own (GRA.embed (knot_full f0)) -* Own (GRA.embed (knot_frag f1)) -* (⌜f1 = f0⌝)) ε
  .
  Proof.
    iIntro. iIntro.
    {
      iMerge A A0. rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. eapply GRA.embed_wf in WF. des. eapply Auth.auth_included in WF. des.
      eapply Excl.extends in WF; ss.
      - des; clarify.
      - ur; ss.
    }
  Qed.

End AUX.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG knotRA Σ}.

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).

  Variable RecStb: SkEnv.t -> list (gname * fspec).
  Variable FunStb: SkEnv.t -> list (gname * fspec).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Let wf (skenv: SkEnv.t): W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ) (f': option (nat -> nat)) (fb': option block),
        (<<SRC: mrps_src0 = (mr, tt↑)>>) /\
        (<<TGT: mrps_tgt0 = (ε, fb'↑)>>) /\
        (<<SIM: (iHyp (Own (GRA.embed (knot_full f'))) mr)>>) /\
        (<<SOME: forall f (FUN: f' = Some f),
            exists fb fn,
              (<<BLK: fb' = Some fb>>) /\
              (<<FN: skenv.(SkEnv.blk2id) fb = Some fn>>) /\
              (<<FIND: List.find (fun '(_fn, _) => dec fn _fn) (FunStb skenv) = Some (fn, fun_gen RecStb skenv f)>>)>>)
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

  Theorem correct: ModPair.sim (Knot1.Knot RecStb FunStb GlobalStb) Knot0.Knot.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf skenv); et; ss.
    2: { eexists. exists None. esplits; ss. eexists. eapply URA.unit_id. }
    econs; ss; [|econs; ss].
    { init. unfold recF, ccall. harg_tac.
      destruct x as [f n]. ss. des. subst.
      iRefresh. do 2 iDestruct PRE. iPure A. des; clarify.
      eapply Any.upcast_inj in A. des; clarify. steps.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify. astart 1.
      assert (f' = Some f); subst.
      { hexploit knot_ra_merge; et. intro T. iSpecialize T SIM. iSpecialize T PRE. iPure T. auto. }
      hexploit SOME; eauto. clear SOME. i. des. clarify. steps.
      rewrite Any.upcast_downcast. ss. steps. rewrite FN. ss. steps.
      hexploit (SKINCL "rec"); ss; eauto. i. des. rewrite H0. ss. steps.
      acall_tac n (ord_pure (2 * n)) SIM (@URA.unit Σ) PRE; ss.
      { eapply FunStb_incl. eauto. }
      { splits; ss. split; ss. iRefresh. iSplitR PRE; ss.
        red. red. esplits; eauto.
        { eapply SKWF. eauto. }
        { eapply RecStb_incl. des_ifs. }
      }
      { splits; ss. eauto with ord_step. }
      { esplits; eauto. i. clarify. esplits; eauto. }
      ss. iRefresh. do 2 iDestruct POST. clarify. iPure POST.
      eapply Any.upcast_inj in POST. des; clarify.
      steps. rewrite Any.upcast_downcast in _UNWRAPN. clarify.
      astop. force_l. eexists.
      hret_tac SIM0 A; ss.
      { split; ss. iRefresh. iSplitL A; ss. }
      { esplits; eauto. }
    }
    { init. unfold knotF, ccall. harg_tac.
      ss. des. subst.
      iRefresh. do 2 iDestruct PRE. iPure PRE. des; clarify.
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
      { split; ss. esplits; eauto. iRefresh. iSplitR A; eauto. red. red. esplits; eauto.
        { eapply SKWF; eauto. }
        { eapply RecStb_incl; eauto. }
      }
      { esplits; eauto. i. clarify. esplits; eauto. }
    }
  Qed.

End SIMMODSEM.
