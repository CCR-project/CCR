Require Import Stack1 Client1 Mem1 Mem2.
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
Require Import Logic YPM.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.
























Require Import HTactics.
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


















Section AUX.
  Context `{Σ: GRA.t}.

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

  (* Lemma echo_ra_merge2 *)
  (*       ll0 ns0 ll1 ns1 *)
  (*   : *)
  (*     iHyp (Own (GRA.embed (echo_black ll0 ns0)) -* Own (GRA.embed (echo_white ll1 ns1)) *)
  (*               -* (⌜ll1 = ll0 /\ ns1 = ns0⌝ ** Own (GRA.embed (echo_black ll0 ns0)) ** Own (GRA.embed (echo_white ll1 ns1)))) ε *)
  (* . *)
  (* Proof. *)
  (*   iIntro. iIntro. *)
  (*   { *)
  (*     iMerge A A0. rewrite <- own_sep in A. rewrite GRA.embed_add in A. *)
  (*     iOwnWf A. eapply GRA.embed_wf in WF. des. eapply URA.auth_included in WF. des. *)
  (*     Local Transparent URA.add. *)
  (*     rr in WF. des. cbn in WF. *)
  (*     Local Opaque URA.add. *)
  (*     des_ifs. *)
  (*     rewrite <- GRA.embed_add in A. rewrite own_sep in A. iDestruct' A. *)
  (*     iSplitL A; ss. *)
  (*     - iSplitP; ss. *)
  (*   } *)
  (* Qed. *)

  Lemma echo_ra_merge
        ll0 ns0 ll1 ns1
    :
      (* iHyp (Own (GRA.embed (echo_black ll0 ns0)) -* Own (GRA.embed (echo_white ll1 ns1)) -* (⌜ll1 = ll0 /\ ns1 = ns0⌝)) ε *)
      ⌞(Own (GRA.embed (echo_black ll0 ns0)) -* Own (GRA.embed (echo_white ll1 ns1)) -* (⌜ll1 = ll0 /\ ns1 = ns0⌝))⌟
  .
  Proof.
    iIntro; clear A.
    do 2 iIntro.
    {
      iMerge A A0. rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. eapply GRA.embed_wf in WF. des. eapply URA.auth_included in WF. des.
      Local Transparent URA.add.
      rr in WF. des. cbn in WF.
      Local Opaque URA.add.
      des_ifs.
    }
  Qed.

  Lemma echo_ra_white
        ll0 ns0 ll1 ns1
    :
      (* iHyp (Own (GRA.embed (echo_white ll0 ns0)) -* Own (GRA.embed (echo_white ll1 ns1)) -* ⌜False⌝) ε *)
      ⌞(Own (GRA.embed (echo_white ll0 ns0)) -* Own (GRA.embed (echo_white ll1 ns1)) -* ⌜False⌝)⌟
  .
  Proof.
    iIntro; clear A.
    do 2 iIntro.
    {
      exfalso. iMerge A A0.
      rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. clear - WF. apply GRA.embed_wf in WF. des. ss.
    }
  Qed.

  Lemma echo_ra_black
        ll0 ns0 ll1 ns1
    :
      (* iHyp (Own (GRA.embed (echo_black ll0 ns0)) -* Own (GRA.embed (echo_black ll1 ns1)) -* ⌜False⌝) ε *)
      ⌞(Own (GRA.embed (echo_black ll0 ns0)) -* Own (GRA.embed (echo_black ll1 ns1)) -* ⌜False⌝)⌟
  .
  Proof.
    iIntro; clear A.
    do 2 iIntro.
    {
      exfalso. iMerge A A0.
      rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. clear - WF. apply GRA.embed_wf in WF. des. ss.
    }
  Qed.
End AUX.
Global Opaque _APC.



Ltac iUpdate H :=
  eapply upd_update in H; [|on_gwf ltac:(fun GWF => eapply wf_downward; [|eapply GWF]); eexists ε; r_equalize; r_solve; fail];
  let GWF := fresh "GWF" in
  let wf := fresh "WF" in
  let upd := fresh "UPD" in
  destruct H as [? [H [wf upd]]];
  on_gwf ltac:(fun _GWF => eassert(GWF: ☀) by
                   (split; [etrans; [apply _GWF|etrans; [|apply upd]]; eapply URA.extends_updatable; r_equalize; r_solve; fail|exact wf]);
                           clear wf upd; iRefresh; clear _GWF).

Ltac until_bar TAC :=
  (on_last_hyp ltac:(fun id' =>
                       match type of id' with
                       | IPROPS => intros
                       | _ => TAC id'; revert id'; until_bar TAC
                       end)).

Ltac rr_until_bar := until_bar ltac:(fun H => rr in H).
Ltac r_until_bar := until_bar ltac:(fun H => r in H).

Ltac iImpure H := let name := fresh "my_r" in
                  specialize (H ε URA.wf_unit I); rewrite intro_iHyp in H;
                  on_gwf ltac:(fun GWF => rewrite <- URA.unit_id in GWF; set (name:=ε) in GWF, H; clearbody name).
Ltac iMod H :=
  match type of H with
  | Impure _ => iImpure H
  | iHyp (⌜ _ ⌝) _ => iPure H
  | iHyp ( |=> _ ) _ => iUpdate H
  | _ => fail
  end
.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.
  Context `{@GRA.inG Echo1.echoRA Σ}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  Eval compute in (@URA.car Mem1._memRA).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ) (ll: val),
        (<<SRC: mrps_src0 = Maps.add "Echo" (mr, tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "Echo" (ε, ll↑) Maps.empty>>) /\
        (* (<<SIM: (iHyp (⌜ll = Vnullptr⌝ ∨ (Exists ns, (Own(GRA.embed(echo_black ns))) ** is_list ll (List.map Vint ns))) mr)>>) *)
        (* (<<SIM: (iHyp (Exists ns, (Own(GRA.embed(echo_black ns))) *)
        (*                             ** (is_list ll (List.map Vint ns) ∨ (Own(GRA.embed(echo_white ns))))) mr)>>) *)
        (<<SIM: (iHyp (Exists ns, ((Own(GRA.embed(echo_black ll ns))) ** is_list ll (List.map Vint ns)) ∨ (Own(GRA.embed(echo_white ll ns)))) mr)>>)
  .

  Local Opaque is_list.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.
  Opaque points_to.

  Lemma gwf_update_cur: forall past cur0 cur1, cur0 = cur1 -> __gwf_mark__ past cur0 -> __gwf_mark__ past cur1. i. subst. eauto. Qed.
  Lemma gwf_dummy: (__gwf_mark__ ε ε). Proof. split; try refl. apply URA.wf_unit. Qed.

  Theorem correct: ModSemPair.sim Echo1.EchoSem Echo0.EchoSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
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
      unfold body_to_tgt. unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.

      hcall_tac __ __ (A, A0) PRE (@URA.unit Σ); ss; et.
      { esplits; ss; et. eexists; iRefresh. left; iRefresh. iSplitL A; ss.
        - iApply A; ss.
        - iApply A0; ss.
      }
      des; subst. rewrite Any.upcast_downcast. steps. rewrite Any.upcast_downcast. steps.



      iDestruct SIM. destruct SIM as [SIM|SIM]; iRefresh; cycle 1.
      { hexploit echo_ra_white; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T PRE. iMod T; des; ss. }
      iDestruct SIM. subst.
      assert(ll0 = ll /\ x = ns); des; subst.
      { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T PRE. iMod T; des; ss. }
      subst.




      destruct (unint vret_src) eqn:T; cycle 1.
      { steps. unfold triggerUB. steps. }
      destruct vret_src; ss. clarify. steps.

      destruct (dec z (- 1)%Z).
      - subst. ss. steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ __ (A, SIM) (@URA.unit Σ) PRE; ss; et.
        { instantiate (2:= (_, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss; et. }
        { esplits; ss; et. }
        { esplits; ss; et. exists ns; iRefresh. left; iRefresh. iSplitL SIM; ss. }
        steps.
        hret_tac mr (@URA.unit Σ); ss.
        { eapply URA.extends_updatable. esplit. r_equalize; r_solve. }
        { iRefresh. iDestruct SIM0. esplits; eauto. eexists; iRefresh. eauto. }
      - steps.
        force_l. eexists 1. steps. rewrite Any.upcast_downcast. ss. steps.

        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("push", [ll; Vint z]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ (ord_pure 2) PRE SIM A; ss; et.
        { instantiate (1:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply A; ss. }
        { esplits; ss; et. exists ns; iRefresh. right; iRefresh; ss. }
        des; iRefresh. do 2 iDestruct POST0. iMod A. subst. apply Any.upcast_inj in A. des; clarify.
        iDestruct SIM0. destruct SIM0; iRefresh.
        { iDestruct H1. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T H1. iMod T; des; ss. }

        rename H1 into A.
        assert(ll0 = ll /\ x8 = ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T A. iMod T; des; ss. }




        iMerge A SIM. rewrite <- own_sep in A. rewrite GRA.embed_add in A. rewrite URA.add_comm in A.
        eapply own_upd in A; cycle 1; [|rewrite intro_iHyp in A;iMod A].
        { eapply GRA.embed_updatable. instantiate (1:= echo_black x (z :: ns) ⋅ echo_white x (z :: ns)).
          eapply URA.auth_update. rr. ii. des; ss. destruct ctx; ss; clarify.
        }
        rewrite <- GRA.embed_add in A. rewrite own_sep in A. iDestruct A. subst.



        rewrite unfold_APC. steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast in *. steps.

        hcall_tac __ ord_top (POST0, A) (@URA.unit Σ) A0; ss; et.
        { instantiate (1:=(_, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss; et. }
        { esplits; ss; eauto. exists (z :: ns); iRefresh. left; iRefresh. iSplitL A; ss. }
        steps.
        hret_tac mr0 (@URA.unit Σ); ss.
        { eapply URA.extends_updatable; et. r_equalize; r_solve. }
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
      - unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
        rewrite Any.upcast_downcast. steps. iMod A0. subst.
        hret_tac x3 (@URA.unit Σ); ss. (********************* TODO **************************************)
        { eapply URA.extends_updatable. esplit. r_equalize; r_solve. }
        { iRefresh. esplits; ss; eauto. exists nil; iRefresh. left; iRefresh. iSplitL A; ss. } (************ TODO ************)
      - rewrite Any.upcast_downcast. steps. do 4 iDestruct A0. iMod A0. subst. ss.
        unfold interp_hCallE_tgt, APC. steps. force_l. exists 3. steps.

        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("alloc", [Vint 1]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ (ord_pure 1) PRE (A, A1, A2) (@URA.unit Σ); ss; et.
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




        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("pop2", [Vptr hd 0; Vptr tmp 0]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ (ord_pure 2) SIM A (A0, A2); ss; et.
        { instantiate (1:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss.
          iSplitR (A0); ss; et.
          - iSplitP; ss. eauto.
          - eexists; iRefresh. eauto.
        }
        { esplits; ss; et. eexists; iRefresh. right; iRefresh; ss; et. }
        des; iRefresh. iDestruct SIM0. do 3 iDestruct POST. iMod POST. subst.
        apply_all_once Any.upcast_inj. des; clarify. steps.
        rewrite Any.upcast_downcast in *. clarify.
        rename SIM0 into SIM. destruct SIM as [SIM|SIM]; iRefresh.
        { iDestruct SIM. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }
        assert(ll = Vptr hd 0 /\ x = z :: ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }



        iMerge A SIM. rewrite <- own_sep in A. rewrite GRA.embed_add in A.
        eapply own_upd in A; cycle 1; [|rewrite intro_iHyp in A;iMod A].
        { eapply GRA.embed_updatable. instantiate (1:= echo_black v (ns) ⋅ echo_white v (ns)).
          eapply URA.auth_update. rr. ii. des; ss. destruct ctx; ss; clarify.
        }
        rewrite <- GRA.embed_add in A. rewrite own_sep in A. iDestruct A.



        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("load", [Vptr tmp 0]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ (ord_pure 1) A2 (A, A1) A0; ss; et.
        { instantiate (1:=(_, _, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. eauto. }
        { esplits; ss; et. eexists; iRefresh. right; iRefresh; ss; et. }
        des; iRefresh. iDestruct SIM. iDestruct POST. iMod A0. subst.
        apply_all_once Any.upcast_inj. des; clarify. steps.
        rewrite Any.upcast_downcast in *. clarify.
        destruct SIM as [SIM|SIM]; iRefresh.
        { iDestruct SIM. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }
        assert(v = ll /\ x = ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }





        rewrite unfold_APC. steps.
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
        hret_tac mr3 (@URA.unit Σ); ss.
        { eapply URA.extends_updatable. r_equalize; r_solve. }
        { iRefresh. esplits; eauto. eexists; iRefresh. eauto. }
    }
  Unshelve.
    all: ss.
    all: try (by repeat econs; et).
  Qed.

End SIMMODSEM.


