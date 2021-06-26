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

Require Import HTactics ProofMode Invariant TODOYJ.

Set Implicit Arguments.

Local Open Scope nat_scope.





(* copied from BW01proof *)
Section AUX.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG knotRA Σ}.
  Lemma knot_ra_merge
        f0 f1
    :
      (OwnM (knot_full f0)) -∗ OwnM (knot_frag f1) -∗ (⌜f1 = f0⌝).
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H" as WF. iPureIntro.
    eapply Auth.auth_included in WF. des.
    eapply Excl.extends in WF; ss.
    - des; clarify.
    - ur; ss.
  Qed.

  Lemma knot_frag_unique
        f0 f1
    :
      (OwnM (knot_frag f0)) -∗ OwnM (knot_frag f1) -∗ (⌜False⌝).
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H" as WF. exfalso.
    ur in WF. ur in WF. ss.
  Qed.

  Lemma knot_full_unique
        f0 f1
    :
      (OwnM (knot_full f0)) -∗ OwnM (knot_full f1) -∗ (⌜False⌝).
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H" as WF. exfalso.
    ur in WF. ur in WF. ss.
  Qed.
End AUX.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).

  Variable RecStb: SkEnv.t -> gname -> option fspec.
  Variable FunStb: SkEnv.t -> gname -> option fspec.
  Variable GlobalStb: SkEnv.t -> gname -> option fspec.

  Definition inv (skenv: SkEnv.t): iProp :=
    (∃ (f': option (nat -> nat)) (fb': val),
        (⌜forall f (EQ: f' = Some f),
              exists fb,
                (<<BLK: fb' = Vptr fb 0>>) /\
                (<<FN: fb_has_spec skenv (FunStb skenv) fb (fun_gen RecStb skenv f)>>)⌝)
          ** (OwnM (knot_full f'))
          ** (OwnM (var_points_to skenv "_f" fb')))%I.

  Let wf (skenv: SkEnv.t): _ -> W -> Prop :=
    @inv_wf
      _ _
      unit
      (fun _ _ _ => inv skenv)
      top4.

  Hypothesis RecStb_incl: forall skenv,
      stb_incl (to_stb KnotRecStb) (RecStb skenv).

  Hypothesis FunStb_incl: forall skenv,
      stb_incl (FunStb skenv) (GlobalStb skenv).

  Variable MemStb_incl: forall skenv,
      stb_incl (to_stb MemStb) (GlobalStb skenv).


  Theorem correct: ModPair.sim (Knot1.Knot RecStb FunStb GlobalStb) Knot0.Knot.
  Proof.
    econs; ss.
    i. econstructor 1 with (wf:=wf (Sk.load_skenv sk)) (le:=inv_le top2); et; ss; cycle 2.
    { eexists (inl _). red. econs.
      { eapply to_semantic. ss.
        iIntros "[H0 H1]". unfold inv. iExists None, _. iFrame. iPureIntro. ss. }
      { ss. }
    }
    { eapply inv_le_PreOrder. ss. }
    eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF.
    hexploit (SKINCL "rec"); ss; eauto. intros [blk0 FIND0].
    hexploit (SKINCL "_f"); ss; eauto. intros [blk1 FIND1].

    econs; ss; [|econs; ss].
    { init. unfold recF, ccall.

      (* arg *)
      iarg. destruct x as [f n]. ss. mDesAll. des. clarify.
      rewrite Any.upcast_downcast. steps. astart 2.

      (* open invariant *)
      mUnfold inv in "INV". mDesAll.
      mAssertPure _.
      { iApply (knot_ra_merge with "A2 A"). } subst.
      rewrite FIND1. steps. acatch.
      { eapply MemStb_incl. stb_tac. ss. }

      (* call with the opened invariant *)
      icall_open _ (_, _, _) with "A1".
      { ss. }
      { iModIntro. iSplitL; ss. iSplitL; ss. iSplitR; ss.
        iEval (unfold var_points_to) in "A1". rewrite FIND1. iFrame. }
      { split; ss. eauto with ord_step. }

      mDesAll. subst. rewrite Any.upcast_downcast. steps.
      hexploit PURE; auto. i. des; clarify. inv FN. inv SPEC. ss. steps.
      rewrite FBLOCK. steps. rewrite FIND0. steps. acatch.
      { eapply FunStb_incl. eapply FIND. }

      (* close invariant *)

      (* call with the closed invariant *)
      icall_weaken (fun_gen RecStb sk f) (ord_pure (2 * n)) _ _ with "*".
      { et. }
      { et. }
      { iModIntro. iFrame. iSplitL; ss.
        { iEval (unfold inv).  iExists _, _. iFrame.
          iEval (unfold var_points_to). rewrite FIND1. iFrame. iPureIntro. ss. }
        { iPureIntro. splits; ss. esplits; et. econs.
          { eapply SKWF. eauto. }
          econs.
          { eapply RecStb_incl. des_ifs. }
          { refl. }
        }
      }
      { split; ss. eauto with ord_step. }
      mDesAll. subst. rewrite Any.upcast_downcast. steps.
      astop. steps. force_l. eexists. steps.

      (* ret *)
      iret _; ss. iModIntro. iFrame. et.
    }
    { init. unfold knotF, ccall.

      (* arg *)
      iarg. mDesAll. des. clarify.
      rewrite Any.upcast_downcast. steps. astart 1.

      (* open invariant *)
      mUnfold inv in "INV". mDesAll.
      mAssertPure _.
      { iApply (knot_ra_merge with "A2 A"). } subst.
      rewrite FIND1. steps. acatch.
      { eapply MemStb_incl. stb_tac. ss. }

      (* call with the opened invariant *)
      icall_open _ (_, _, _) with "A1".
      { ss. }
      { iModIntro. iSplitL; ss.
        iSplitL; ss. iExists _. iSplitR; ss.
        iEval (unfold var_points_to) in "A1". rewrite FIND1. ss. }
      { split; ss. eauto with ord_step. }
      mDesAll. subst. steps. rewrite FIND0. steps. astop.

      (* close invariant *)

      (* update resource *)
      mAssert _ with "A A2".
      { iCombine "A2" "A" as "A". iApply (OwnM_Upd with "A").
        instantiate (1:= knot_full (Some x) ⋅ knot_frag (Some x)).
        eapply Auth.auth_update. rr. ii. des; ss. ur in FRAME. ur.
        destruct ctx0; ss; clarify. }
      mUpd "A1". mDesOwn "A1".

      (* ret *)
      force_l. eexists. steps. iret _; ss.
      iModIntro. iEval (unfold inv, var_points_to). rewrite FIND1.
      iSplitL "A1 POST"; ss.
      { iExists _, _. iSplitR "POST"; ss. iSplitR; ss.
        iPureIntro. i. clarify. esplits; eauto. }
      { iFrame. iSplit; ss. iPureIntro. esplits; et. econs.
        { eapply SKWF. et. }
        econs.
        { eapply RecStb_incl. ss. }
        { refl. }
      }
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
