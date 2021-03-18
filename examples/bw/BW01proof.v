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
Ltac harg_tac :=
  HTactics.harg_tac;
  match goal with
  | [H: URA.wf ?cur |- _] =>
    let name := fresh "GWF" in
    assert(name: __gwf_mark__ cur cur) by (split; [refl|exact H]); clear H
  end.

Ltac hcall_tac x o MR_SRC1 FR_SRC1 RARG_SRC :=
  let mr_src1 := r_gather MR_SRC1 in
  let fr_src1 := r_gather FR_SRC1 in
  let rarg_src := r_gather RARG_SRC in
  (* let tac0 := etrans; [on_gwf ltac:(fun GWF => apply GWF)|eapply URA.extends_updatable; r_equalize; r_solve] in *)
  (* let tac0 := idtac in *)
  let tac0 := etrans; [etrans; [|on_gwf ltac:(fun GWF => apply GWF)]|]; eapply URA.extends_updatable; r_equalize; r_solve; fail in
  let tac1 := (on_gwf ltac:(fun H => clear H);
               let WF := fresh "WF" in
               let tmp := fresh "_tmp_" in
               let GWF := fresh "GWF" in
               intros ? ? ? ? ? WF; cbn in WF; desH WF; subst;
               esplits; ss; et; intros tmp ?; assert(GWF: ☀) by (split; [refl|exact tmp]); clear tmp; iRefresh; iClears') in
  prep;
  match x with
  | ltac_wild =>
    match o with
    | ltac_wild => eapply (hcall_clo _ (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src)); [tac0|lia|..|tac1]
    | _ => eapply (hcall_clo _ (o:=o) (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src)); [tac0|lia|..|tac1]
    end
  | _ => eapply (hcall_clo x (o:=o) (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src)); [tac0|lia|..|tac1]
  end
.
Ltac hret_tac MR_SRC RT_SRC :=
  let mr_src1 := r_gather MR_SRC in
  let fr_src1 := r_gather RT_SRC in
  HTactics.hret_tac mr_src1 fr_src1
.

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
      Local Transparent URA.add.
      rr in WF. des. cbn in WF.
      Local Opaque URA.add.
      des_ifs.
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
      { eapply URA.extends_updatable. esplit. r_equalize; r_solve. }
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
        eapply URA.auth_update. rr. ii. des; ss. destruct ctx; ss; clarify.
      }
      rewrite <- GRA.embed_add in SIM. rewrite own_sep in SIM. iDestruct SIM. clarify.
      hret_tac SIM A.
      { etransitivity; [apply GWF0|].
        eapply URA.extends_updatable. esplit. r_equalize; r_solve. }
      { split; eauto. iRefresh. replace (negb (Z.odd n)) with (Z.odd (n+1)); auto.
        rewrite Z.odd_add. ss. }
      { unfold wf. esplits; eauto. }
    }
  Qed.

End SIMMODSEM.
