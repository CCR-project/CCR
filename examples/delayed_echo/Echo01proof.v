Require Import Stack1 Client1 Mem1.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef Echo0 Echo1 SimModSem.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import TODOYJ.
Require Import HTactics Logic YPM.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.





Section AUX.
  Context `{Σ: GRA.t}.

  Context `{@GRA.inG Mem1.memRA Σ}.
  Lemma unfold_is_list: forall ll xs, is_list ll xs =
    match xs with
    | [] => ⌜ll = Vnullptr⌝
    | xhd :: xtl =>
      Exists lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (Own (GRA.embed ((lhd,0%Z) |-> [xhd; ltl])))
                                 ** is_list ltl xtl
    end
  .
    { i. destruct xs; ss. }
  Qed.

  Context `{@GRA.inG Echo1.echoRA Σ}.

  Lemma echo_ra_merge
        ll0 ns0 ll1 ns1
    :
      ⌞(Own (GRA.embed (echo_black ll0 ns0)) -* Own (GRA.embed (echo_white ll1 ns1)) -* (⌜ll1 = ll0 /\ ns1 = ns0⌝))⌟
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

  Lemma echo_ra_white
        ll0 ns0 ll1 ns1
    :
      ⌞(Own (GRA.embed (echo_white ll0 ns0)) -* Own (GRA.embed (echo_white ll1 ns1)) -* ⌜False⌝)⌟
  .
  Proof.
    iIntro; clear A.
    do 2 iIntro.
    {
      exfalso. iMerge A A0.
      rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. clear - WF. apply GRA.embed_wf in WF. des. do 2 ur in WF. ss.
    }
  Qed.

  Lemma echo_ra_black
        ll0 ns0 ll1 ns1
    :
      ⌞(Own (GRA.embed (echo_black ll0 ns0)) -* Own (GRA.embed (echo_black ll1 ns1)) -* ⌜False⌝)⌟
  .
  Proof.
    iIntro; clear A.
    do 2 iIntro.
    {
      exfalso. iMerge A A0.
      rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. clear - WF. apply GRA.embed_wf in WF. des. do 2 ur in WF. ss.
    }
  Qed.
End AUX.
Global Opaque _APC.






Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.
  Context `{@GRA.inG Echo1.echoRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).
  Eval compute in (@URA.car Mem1._memRA).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ) (ll: val),
        (<<SRC: mrps_src0 = (mr, tt↑)>>) /\
        (<<TGT: mrps_tgt0 = (ε, ll↑)>>) /\
        (<<SIM: (iHyp (Exists ns, ((Own(GRA.embed(echo_black ll ns))) ** is_list ll (List.map Vint ns)) ∨ (Own(GRA.embed(echo_white ll ns)))) mr)>>)
  .

  Local Opaque is_list.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.
  Opaque points_to.

  Theorem correct: ModSemPair.sim Echo1.EchoSem Echo0.EchoSem.
  Proof.
    econstructor 1 with (wf:=wf); et; swap 2 3.
    { ss. unfold alist_add; cbn. esplits; ss; eauto. hexploit gwf_dummy; i. eexists nil; ss; iRefresh.
      rewrite unfold_is_list. left; iRefresh. iSplitP; ss. eexists ε. rewrite URA.unit_id; ss.
    }

    Opaque URA.add.
    econs; ss.
    { unfold echoF, echo_body. init.
      harg_tac. des_ifs_safe. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      iRefresh. do 2 iDestruct PRE. iMod A. iMod A0. clarify.
      iDestruct SIM.
      destruct SIM as [A|A]; iRefresh; cycle 1.
      { hexploit echo_ra_white; et. intro T. iMod T. iSpecialize T A. iSpecialize T PRE. iMod T; des; ss. }

      iDestruct A. subst.
      rename x into ns. rename x0 into ns0.
      assert(l = ns /\ v = ll); des; subst.
      { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T PRE. iMod T; des; ss. }




      steps. unfold hcall, ccall. steps.
      force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.

      hcall_tac __ __ (A, A0) PRE (@URA.unit Σ); ss; et.
      { esplits; ss; et. eexists; iRefresh. left; iRefresh. iSplitL A; ss.
        - iApply A; ss.
        - iApply A0; ss.
      }
      des; subst. rewrite Any.upcast_downcast. steps.
      rewrite Any.upcast_downcast in _UNWRAPU. clarify.



      iDestruct SIM. destruct SIM as [SIM|SIM]; iRefresh; cycle 1.
      { hexploit echo_ra_white; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T PRE. iMod T; des; ss. }
      iDestruct SIM. subst.
      assert(ll0 = ll /\ x = ns); des; subst.
      { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T PRE. iMod T; des; ss. }
      subst.




      destruct (unint v) eqn:T; cycle 1.
      { steps. }
      destruct v; ss. clarify. steps.

      destruct (dec z (- 1)%Z).
      - subst. ss. steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ __ (A, SIM) (@URA.unit Σ) PRE; ss; et.
        { instantiate (2:= (_, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss; et. }
        { esplits; ss; et. }
        { esplits; ss; et. exists ns; iRefresh. left; iRefresh. iSplitL SIM; ss. }
        steps.
        hret_tac SIM0 (@URA.unit Σ); ss.
        { iRefresh. iDestruct SIM0. esplits; eauto. eexists; iRefresh. eauto. }
      - steps. astart 10. rewrite Any.upcast_downcast. ss. steps.
        acall_tac __ (ord_pure 2) PRE SIM A; ss; et.
        { instantiate (1:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply A; ss. }
        { esplits; ss; et. exists ns; iRefresh. right; iRefresh; ss. }
        ss. des; iRefresh. do 2 iDestruct POST0. iMod A. subst. apply Any.upcast_inj in A. des; clarify.
        iDestruct SIM0. destruct SIM0; iRefresh.
        { iDestruct H1. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T H1. iMod T; des; ss. }

        rename H1 into A.
        assert(ll0 = ll /\ x8 = ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T A. iMod T; des; ss. }




        iMerge A SIM. rewrite <- own_sep in A. rewrite GRA.embed_add in A. rewrite URA.add_comm in A.
        eapply own_upd in A; cycle 1; [|rewrite intro_iHyp in A;iMod A].
        { eapply GRA.embed_updatable. instantiate (1:= echo_black x (z :: ns) ⋅ echo_white x (z :: ns)).
          eapply Auth.auth_update. rr. ii. des; ss. ur in FRAME. ur. destruct ctx; ss; clarify.
        }
        rewrite <- GRA.embed_add in A. rewrite own_sep in A. iDestruct A. subst.

        steps. rewrite Any.upcast_downcast in *. clarify. astop.
        steps. force_l; stb_tac; clarify.
        steps. rewrite Any.upcast_downcast in *. ss. steps.
        hcall_tac __ ord_top (POST0, A) (@URA.unit Σ) A0; ss; et.
        { instantiate (1:=(_, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss; et. }
        { esplits; ss; eauto. exists (z :: ns); iRefresh. left; iRefresh. iSplitL A; ss. }
        steps.
        hret_tac SIM (@URA.unit Σ); ss.
        { esplits; eauto. }
    }
    econs; ss.
    { unfold echo_finishF, echo_finish_body. init. harg_tac; des_ifs_safe; iRefresh. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      do 2 iDestruct PRE. iMod A. iMod A0. clarify.
      iDestruct SIM.
      destruct SIM as [A|A]; iRefresh; cycle 1.
      { hexploit echo_ra_white; et. intro T. iMod T. iSpecialize T A. iSpecialize T PRE. iMod T; des; ss. }

      iDestruct A. subst.
      rename x into ns. rename x0 into ns0.
      assert(v = ll /\ l = ns).
      { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T PRE. iMod T; des; ss. }
      des; subst.




      steps. unfold hcall, ccall. rewrite unfold_is_list in A0. destruct ns; ss; steps.
      - rewrite Any.upcast_downcast. steps. iMod A0. subst.
        hret_tac A (@URA.unit Σ); ss.
        { iRefresh. esplits; ss; eauto. exists nil; iRefresh. left; iRefresh. iSplitL A; ss. }
      - rewrite Any.upcast_downcast. steps. do 4 iDestruct A0. iMod A0. subst. ss.
        astart 10. steps.
        acall_tac __ (ord_pure 0) PRE (A, A1, A2) (@URA.unit Σ); ss; et.
        { esplits; try refl; iRefresh. instantiate (1:=1). esplits; ss; et. }
        { esplits; ss; et. eexists; iRefresh. right; iRefresh; ss; et. }
        des; iRefresh. do 2 iDestruct POST. iMod POST. subst.
        apply_all_once Any.upcast_inj. des; clarify. steps. rewrite Any.upcast_downcast in *. clarify.
        iDestruct SIM. destruct SIM as [SIM|SIM]; iRefresh.
        { iDestruct SIM. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }
        assert(ll = (Vptr x 0) /\ x10 = z :: ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }




        rename x into hd. rename x5 into tmp.
        iMerge A1 A2.
        iAssert A1 (is_list (Vptr hd 0) (List.map Vint (z :: ns))).
        { iIntro. rewrite unfold_is_list. cbn.
          iDestruct A2. do 2 eexists; iRefresh.
          iSplitL A.
          { iSplitP; ss; et. }
          { iRefresh; ss. }
        }




        acall_tac __ (ord_pure 2) SIM A (A0, A2); ss; et.
        { instantiate (1:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss.
          iSplitR (A0); ss; et.
          - iSplitP; ss. eauto.
          - eexists; iRefresh. eauto.
        }
        { esplits; ss; et. eexists; iRefresh. right; iRefresh; ss; et. }
        ss. des; iRefresh. iDestruct SIM0. do 3 iDestruct POST. iMod POST. subst.
        apply_all_once Any.upcast_inj. des; clarify. steps.
        rewrite Any.upcast_downcast in *. clarify.
        rename SIM0 into SIM. destruct SIM as [SIM|SIM]; iRefresh.
        { iDestruct SIM. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }
        assert(ll = Vptr hd 0 /\ x = z :: ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }



        iMerge A SIM. rewrite <- own_sep in A. rewrite GRA.embed_add in A.
        eapply own_upd in A; cycle 1; [|rewrite intro_iHyp in A;iMod A].
        { eapply GRA.embed_updatable. instantiate (1:= echo_black v (ns) ⋅ echo_white v (ns)).
          eapply Auth.auth_update. rr. ii. des; ss. ur in FRAME. ur. destruct ctx; ss; clarify.
        }
        rewrite <- GRA.embed_add in A. rewrite own_sep in A. iDestruct A.



        acall_tac __ (ord_pure 0) A2 (A, A1) A0; ss; et.
        { instantiate (1:=(_, _, _)). ss. esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. eauto. }
        { esplits; ss; et. eexists; iRefresh. right; iRefresh; ss; et. }
        ss. des; iRefresh. iDestruct SIM. iDestruct POST. iMod A0. subst.
        apply_all_once Any.upcast_inj. des; clarify. steps.
        rewrite Any.upcast_downcast in *. clarify.
        destruct SIM as [SIM|SIM]; iRefresh.
        { iDestruct SIM. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }
        assert(v = ll /\ x = ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }





        astop. steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ (ord_top) SIM (A, A1, POST) (@URA.unit Σ); ss; et.
        { esplits; ss; et. eexists; iRefresh. right; iRefresh; ss; et. }
        des; iRefresh. subst. iDestruct SIM0.
        rename SIM0 into SIM. destruct SIM as [SIM|SIM]; iRefresh.
        { iDestruct SIM. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }
        assert(ll0 = ll /\ x = ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }



        steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast in *. steps.
        hcall_tac __ (ord_top) (A, A1) POST SIM; ss; et.
        { instantiate (1:= (_, _)). cbn. iRefresh. iSplitP; ss. iSplitP; ss; et. }
        { esplits; ss; et. eexists; iRefresh. left; iRefresh. iSplitL A; ss; et. }
        des; iRefresh. subst. iDestruct SIM0.

        steps.
        hret_tac SIM0 (@URA.unit Σ); ss.
        { iRefresh. esplits; eauto. eexists; iRefresh. eauto. }
    }
  Unshelve.
    all: ss.
    all: try (by repeat econs; et).
  Qed.

End SIMMODSEM.
