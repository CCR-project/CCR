Require Import HoareDef MapHeader MapM MapA SimModSem.
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

Require Import HTactics2 ProofMode STB Invariant.
Require Import Mem1.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.
  Context `{Σ: GRA.t}.

  Context `{@GRA.inG MapRA0 Σ}.
  Context `{@GRA.inG MapRA1 Σ}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := Any.t * Any.t.

  Definition initial_map: iProp :=
    OwnM (Excl.unit, Auth.excl ((fun _ => Excl.just 0%Z): @URA.car (Z ==> (Excl.t Z))%ra) ((fun _ => Excl.just 0%Z): @URA.car (Z ==> (Excl.t Z))%ra)).

  Definition black_map (f: Z -> Z): iProp :=
    OwnM (Excl.unit, Auth.black ((fun k => Excl.just (f k)): @URA.car (Z ==> (Excl.t Z))%ra)).

  Definition unallocated (sz: Z): iProp :=
    OwnM (Excl.unit, Auth.white ((fun k =>
                                    if (Z_gt_le_dec 0 k) then Excl.just 0%Z
                                    else if (Z_gt_le_dec sz k) then Excl.unit else Excl.just 0%Z)
                                  : @URA.car (Z ==> (Excl.t Z))%ra)).

  Lemma initial_map_initialize sz
    :
    initial_map -∗ #=> (black_map (fun _ => 0%Z) ** initial_points_tos sz ** unallocated sz).
  Proof.
  Admitted.

  Lemma initial_map_no_points_to k v
    :
    initial_map -∗ map_points_to k v -∗ ⌜False⌝.
  Proof.
  Admitted.

  Lemma unallocated_range sz k v
    :
    unallocated sz -∗ map_points_to k v -∗ ⌜(0 <= k < sz)%Z⌝.
  Proof.
  Admitted.

  Lemma black_map_get f k v
    :
    black_map f -∗ map_points_to k v -∗ (⌜f k = v⌝).
  Proof.
  Admitted.

  Lemma black_map_set f k w v
    :
    black_map f -∗ map_points_to k w -∗ #=> (black_map (fun n => if Z.eq_dec n k then v else f n) ** map_points_to k v).
  Proof.
  Admitted.

  Let wf: _ -> W -> Prop :=
        @mk_wf
          _ unit
          (fun _ st_src st_tgt =>
             ((∃ f sz, ⌜st_src = f↑ /\ st_tgt = (f, sz)↑⌝ ** black_map f ** unallocated sz ** pending1) ∨ (initial_map ** ⌜st_src = (fun (_: Z) => 0%Z)↑ /\ st_tgt = (fun (_: Z) => 0%Z, 0%Z)↑⌝))%I).

  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Hypothesis STB_set: forall sk, (GlobalStb sk) "set" = Some set_spec.

  Hypothesis PUREINCL: forall sk, stb_pure_incl (GlobalStbM sk) (GlobalStb sk).

  Lemma pending1_unique:
    pending1 -∗ pending1 -∗ False%I.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". exfalso. clear - H2.
    rr in H2. ur in H2. unseal "ra". des.
    rr in H2. ur in H2. unseal "ra". ss.
  Qed.

  Theorem correct: refines2 [MapM.Map GlobalStbM] [MapA.Map GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits. econs; et. eapply to_semantic. iIntros "H". iSplitL "H"; eauto. iApply Own_unit. ss. }
    Local Opaque initial_map black_map map_points_to unallocated.
    econs.
    {
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)
      unfold MapM.initF, MapA.initF, ccallU, ccallN.
      harg. fold wf. ss.
      unfold pending in ACC. mDesAll; des; clarify.
      mDesOr "INVS".
      { mDesAll. mAssertPure False; ss. iApply (pending1_unique with "A A2"). }
      steps. mDesAll. des. subst.
      mAssert _ with "INVS".
      { iApply (initial_map_initialize with "INVS"). }
      mUpd "A". mDesAll.
      harg_tgt.
      { iModIntro. iFrame. iSplits; et. xtra. }
      steps.
      (*** calling APC ***)
      hAPC _.
      { iIntros "A"; iDes. iSplitR "A".
        { iLeft. iExists _, _. iFrame. iSplits; eauto. }
        { iApply "A". }
      }
      { auto. }
      fold wf. steps.
      hret _; ss.
      { iModIntro.
        iDestruct "Q" as "[CLOSED %]". subst. iFrame.
        iDestruct "FR" as "[H0 H1]". iDestruct "H0" as "[H0 | H0]".
        { iDestruct "H0" as (f0 sz0) "[[[% H2] H3] H4]". des; subst.
          iFrame. iSplits; auto.
          iLeft. iExists _, _. iFrame. iPureIntro. eauto.
        }
        { iDes. des; subst. iSplitR "H1"; eauto. }
      }
      { iDestruct "Q" as "[_ %]". des; subst. iPureIntro.
        rr. esplits; eauto.
      }
    }
    econs; ss.
    {
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)
      unfold MapM.getF, MapA.getF, ccallU, ccallN.
      harg. fold wf. destruct x. ss.
      mDesAll; des; clarify.
      mDesOr "INVS".
      2:{ mDesAll. mAssertPure False; ss. iApply (initial_map_no_points_to with "INVS A1"). }
      mDesAll. des; subst.
      mAssertPure (0 ≤ z < a0)%Z.
      { iApply (unallocated_range with "A2 A1"); eauto. }
      mAssertPure _.
      { iApply (black_map_get with "A3 A1"). }
      subst. steps.
      harg_tgt.
      { iModIntro. iFrame. iSplits; et. xtra. }
      steps. force_r; auto. steps.
      (*** calling APC ***)
      hAPC _.
      { iIntros "A"; iDes. iSplitR "A2".
        { iLeft. iExists _, _. iFrame. iSplits; auto. }
        { iApply "A2". }
      }
      { auto. }
      fold wf. steps.
      hret _; ss.
      { iModIntro.
        iDestruct "Q" as "[CLOSED %]". subst. iFrame.
        iDestruct "FR" as "[H0 H1]". iDestruct "H0" as "[H0 | H0]".
        2:{ iDes. iPoseProof (initial_map_no_points_to with "H0 H1") as "H"; ss. }
        iDestruct "H0" as (f0 sz0) "[[[% H2] H3] H4]". des; subst.
        iFrame. iSplits; auto.
        iLeft. iExists _, _. iFrame. iPureIntro. eauto.
      }
      { iDestruct "Q" as "[_ %]". subst. iPureIntro.
        rr. esplits; eauto.
      }
    }

    econs; ss.
    {
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)
      unfold MapM.setF, MapA.setF, ccallU, ccallN.
      harg. fold wf. destruct x as [[? ?] ?]. ss.
      mDesAll; des; clarify.
      mDesOr "INVS".
      2:{ mDesAll. mAssertPure False; ss. iApply (initial_map_no_points_to with "INVS A1"). }
      mDesAll. des; subst.
      mAssertPure (0 ≤ z < a0)%Z.
      { iApply (unallocated_range with "A2 A1"); eauto. }
      steps.
      mAssert _ with "A3 A1".
      { iApply (black_map_set with "A3 A1"). }
      mUpd "A4". mDesAll.
      harg_tgt.
      { iModIntro. iFrame. iSplits; et. xtra. }
      steps. force_r; auto. steps.
      (*** calling APC ***)
      hAPC _.
      { iIntros "A"; iDes. iSplitR "A".
        { iLeft. iExists _, _. iFrame. iSplits; eauto. }
        { iApply "A". }
      }
      { auto. }
      fold wf. steps.
      hret _; ss.
      { iModIntro.
        iDestruct "Q" as "[CLOSED %]". subst. iFrame.
        iDestruct "FR" as "[H0 H1]". iDestruct "H0" as "[H0 | H0]".
        2:{ iDes. iPoseProof (initial_map_no_points_to with "H0 H1") as "H"; ss. }
        iDestruct "H0" as (f0 sz0) "[[[% H2] H3] H4]". des; subst.
        iFrame. iSplits; auto.
        iLeft. iExists _, _. iFrame. iPureIntro. eauto.
      }
      { iDestruct "Q" as "[_ %]". subst. iPureIntro.
        rr. esplits; eauto.
      }
    }
    econs; ss.
    {
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)
      unfold MapM.set_by_userF, MapA.set_by_userF, ccallU, ccallN.
      harg. fold wf. destruct x. ss.
      mDesOr "INVS".
      2:{ mDesAll. mAssertPure False; ss. iApply (initial_map_no_points_to with "INVS A1"). }
      mDesAll. des; subst. steps.
      harg_tgt.
      { iModIntro. iFrame. iSplits; et. xtra. }
      steps. rewrite _UNWRAPU. rewrite STB_set. steps.
      rewrite STB_setM in *. clarify. hcall _ _.
      { instantiate (1:=(_, _, _)). ss. iModIntro.
        iSplits; ss. iDes. iFrame. iSplits; ss; eauto.
        { instantiate (1:=True%I). iSplit; ss. iLeft.
          iExists _, _. iFrame. iPureIntro. eauto.
        }
      }
      { i. ss. iIntros "H". iDes. subst. eauto. }
      ss. mDesAll. subst.
      hpost_tgt.
      { iModIntro. iFrame. iSplits; ss; et. xtra. }
      steps. hret _; ss.
      { iModIntro.
        iDestruct "Q" as "[CLOSED %]". subst. iFrame.
        iDestruct "FR" as "[H0 H1]". iDestruct "H1" as "[H1 | H1]".
        2:{ iDes. iPoseProof (initial_map_no_points_to with "H1 H0") as "H"; ss. }
        iDestruct "H1" as (f0 sz0) "[[[% H2] H3] H4]". des; subst.
        iSplitR "H0"; eauto. iLeft. iExists _, _. iFrame. iPureIntro. eauto.
      }
      { iDestruct "Q" as "[_ %]". subst. iPureIntro.
        rr. esplits; eauto.
      }
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
