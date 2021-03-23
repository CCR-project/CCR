Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef BW0 BW1 SimModSem.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import TODOYJ Logic YPM.
Require Import HTactics.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.




(**************** TODO: remove this redundancy *************************)
(**************** TODO: remove this redundancy *************************)
(**************** TODO: remove this redundancy *************************)
Lemma unfold_APC: forall n, _APC n =
  match n with
  | 0 => Ret tt
  | S n => break <- trigger (Choose _);;
           if break: bool
           then Ret tt
           else '(fn, varg) <- trigger (Choose _);;
                trigger (hCall true fn varg);; _APC n
  end.
  { i. destruct n; ss. }
Qed.
Global Opaque _APC.



Section AUX.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG bwRA Σ}.
  Lemma bw_ra_merge
        b0 b1
    :
      iHyp (Own (GRA.embed (bw_full b0)) -* Own (GRA.embed (bw_frag b1)) -* (⌜b1 = b0⌝)) ε
  .
  Proof.
    iIntro. iIntro.
    {
      iMerge A A0. rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. eapply GRA.embed_wf in WF. des. eapply URA.auth_included in WF. des.
      eapply URA.Excl.extends in WF; ss.
      - des; clarify.
      - ur; ss.
    }
  Qed.

End AUX.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG BW1.bwRA Σ}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ) (n: Z),
        (<<SRC: mrps_src0 = Maps.add "BW" (mr, tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "BW" (ε, n↑) Maps.empty>>) /\
        (<<SIM: (iHyp (Own (GRA.embed (bw_full (Z.odd n)))) mr)>>)
  .

  Opaque URA.unit.

  Theorem correct: ModSemPair.sim BW1.BWSem BW0.BWSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. unfold alist_add; cbn. esplits; ss; eauto.
      exists ε. rewrite URA.unit_id; ss. }

    Opaque URA.add.
    econs; ss.
    { unfold getF. init.
      harg_tac. des. subst. rewrite Any.upcast_downcast. ss.
      iRefresh. iDestruct PRE. iPure A. clarify.
      assert (x = Z.odd n); subst.
      { hexploit bw_ra_merge; et. intro T. iSpecialize T SIM. iSpecialize T PRE. iPure T. auto. }
      unfold body_to_tgt. unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l. exists 0. steps. rewrite unfold_APC. steps.
      rewrite Any.upcast_downcast. force_l. eexists.
      hret_tac SIM PRE.
      { split; eauto. iRefresh. iSplitL PRE; eauto. rr. f_equal.
        rewrite <- Z.negb_odd. rewrite negb_if. des_ifs. }
      { unfold wf. esplits; eauto. }
    }
    econs; ss.
    { unfold flipF. init.
      harg_tac. des. subst. rewrite Any.upcast_downcast. ss.
      iRefresh. iDestruct PRE. iPure A. clarify.
      assert (x = Z.odd n); subst.
      { hexploit bw_ra_merge; et. intro T. iSpecialize T SIM. iSpecialize T PRE. iPure T. auto. }
      unfold body_to_tgt. unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l. exists 0. steps. rewrite unfold_APC. steps.
      rewrite Any.upcast_downcast. force_l. eexists. steps.
      iMerge SIM PRE. rewrite <- own_sep in SIM.
      eapply own_upd in SIM; cycle 1; [|rewrite intro_iHyp in SIM;iUpdate SIM].
      { rewrite GRA.embed_add. eapply GRA.embed_updatable.
        instantiate (1:= bw_full (Z.odd (n+1)) ⋅ bw_frag (Z.odd (n+1))).
        eapply URA.auth_update. rr. ii. des; ss. ur in FRAME. ur. destruct ctx; ss; clarify.
      }
      rewrite <- GRA.embed_add in SIM. rewrite own_sep in SIM. iDestruct SIM. clarify.

      hret_tac SIM A.
      { split; eauto. iRefresh. replace (negb (Z.odd n)) with (Z.odd (n+1)); auto.
        rewrite Z.odd_add. ss. }
      { unfold wf. esplits; eauto. }
    }
  Qed.

End SIMMODSEM.
