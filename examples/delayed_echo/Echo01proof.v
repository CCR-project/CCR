Require Import LinkedList1 Client1 Mem1 Mem2.
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

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.





(******** TODO : remove redundancy with LL01proof ***********)
Ltac iClears' :=
  match goal with
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (([(_, (?src0, _))], ?src1), ?src2) (([(_, (?tgt0, _))], ?tgt1), ?tgt2)) ] =>
    let name := fresh "tmp" in
    let all := constr:(src0 ⋅ src1 ⋅ tgt0 ⋅ tgt1) in
    pose all as name;
    repeat multimatch goal with
           | [H: iHyp ?ph ?rh |- _ ] =>
             tryif r_contains rh all then idtac else clear H
                                                           (* idtac H; *)
                                                           (*   idtac rh; *)
                                                           (*   tryif r_contains rh all then idtac "CONTAINS" else idtac "DROP" *)
           end;
    clear name
  end.

Ltac iSplitP :=
  match goal with
  | |- ᐸ (Pure ?ph) ** ?pg ᐳ =>
    erewrite f_equal; cycle 1; [ instantiate (1 := (ε ⋅ _)); rewrite URA.unit_idl; refl | eapply sepconj_merge; iClears ]
  | |- ᐸ ?ph ** (Pure ?pg) ᐳ =>
    erewrite f_equal; cycle 1; [ instantiate (1 := (_ ⋅ ε)); rewrite URA.unit_id; refl | eapply sepconj_merge; iClears ]
  end
.

Ltac iDestruct' H :=
  match type of H with
  | iHyp (Exists _, _) _ => destruct H as [? H]; iRefresh
  | iHyp (_ ** _) _ =>
    let name0 := fresh "A" in
    apply sepconj_split in H as [? [? [H [name0 ?]]]]; subst; iRefresh
  end.

Ltac iSplitL Hs0 :=
  match goal with
  | |- ᐸ ?ph ** ?pg ᐳ =>
    let tmp := (r_gather Hs0) in
    erewrite f_equal; cycle 1; [instantiate (1 := tmp ⋅ _)|eapply sepconj_merge; [iClears|(*** TODO: We don't use iClears here because there are unresolved existentials.
                                                             use pcm solver and put iClears ***)]]
  end.
Ltac iSplitR Hs0 :=
  match goal with
  | |- ᐸ ?ph ** ?pg ᐳ =>
    let tmp := (r_gather Hs0) in
    erewrite f_equal; cycle 1; [instantiate (1 := _ ⋅ tmp)|eapply sepconj_merge; [(*** TODO: We don't use iClears here because there are unresolved existentials.
                                                             use pcm solver and put iClears ***)|iClears]]
  end.

Ltac iExists' Hs := let rs := r_gather Hs in exists rs.









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
        (* (<<SIM: (iHyp (⌜ll = Vnullptr⌝ ∨ (Exists ns, (Own(GRA.padding(echo_black ns))) ** is_list ll (List.map Vint ns))) mr)>>) *)
        (* (<<SIM: (iHyp (Exists ns, (Own(GRA.padding(echo_black ns))) *)
        (*                             ** (is_list ll (List.map Vint ns) ∨ (Own(GRA.padding(echo_white ns))))) mr)>>) *)
        (<<SIM: (iHyp (Exists ns, ((Own(GRA.padding(echo_black ns))) ** is_list ll (List.map Vint ns)) ∨ (Own(GRA.padding(echo_white ns)))) mr)>>)
  .

  Local Opaque is_list.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.


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
  Opaque _APC.

  Lemma unfold_is_list: forall ll xs, is_list ll xs = 
    match xs with
    | [] => ⌜ll = Vnullptr⌝
    | xhd :: xtl =>
      Exists lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (Own (GRA.padding ((lhd,0%Z) |-> [xhd; ltl])))
                                 ** is_list ltl xtl
    end
  .
    { i. destruct xs; ss. }
  Qed.

  Lemma Own_downward: forall r a0 a1, iHyp (Own r) a0 -> URA.extends a0 a1 -> iHyp (Own r) a1.
  Proof. i. eapply Own_extends; et. Qed.

  Lemma is_list_downward: forall ll xs a0 a1, iHyp (is_list ll xs) a0 -> URA.extends a0 a1 -> iHyp (is_list ll xs) a1.
  Proof.
    admit "ez".
  Qed.

  Lemma wf_downward: forall (r0 r1: Σ) (EXT: URA.extends r0 r1), URA.wf r1 -> URA.wf r0.
  Proof.
    i. rr in EXT. des; subst. eapply URA.wf_mon; et.
  Qed.




  Ltac iOwnWf G :=
    match goal with
    | H:iHyp (Own ?r) ?rh |- _ => check_equal H G; let name := fresh "WF" in assert(name: URA.wf r); [eapply wf_downward; [eapply H|]|]
    end.

  Opaque points_to.

  Theorem correct: ModSemPair.sim Echo1.EchoSem Echo0.EchoSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. unfold alist_add; cbn. esplits; ss; eauto. eexists nil; ss; iRefresh.
      rewrite unfold_is_list. left. eexists _, ε. split; ss.
      { rewrite URA.unit_id; ss. }
      split; ss. refl.
    }

    Opaque URA.add.
    Opaque LinkedListStb EchoStb MemStb.
    econs; ss.
    { init.
      unfold checkWf, forge, discard, put. steps.
      unfold echoF, echo_body. steps.
      iRefresh. do 2 iDestruct _ASSUME0. iPure A. iPure A0. clarify.
      iDestruct SIM.
      destruct SIM as [A|A]; iRefresh; cycle 1.
      { exfalso. iMerge A _ASSUME0. rewrite <- own_sep in A. rewrite GRA.padding_add in A.
        iOwnWf A.
        { clear - _ASSUME. admit "ez - pcm solver". }
        clear - WF. apply GRA.padding_wf in WF. des. ss.
      }

      iDestruct A. subst.
      rename x into ns. rename x0 into ns0.
      assert(ns = ns0).
      { iMerge A _ASSUME0. rewrite <- own_sep in A. rewrite GRA.padding_add in A.
        iOwnWf A.
        { clear - _ASSUME. admit "ez - pcm solver". }
        eapply GRA.padding_wf in WF. des. eapply URA.auth_included in WF. des.
        clear - WF.
        Local Transparent URA.add.
        rr in WF. des. ss. des_ifs.
        Local Opaque URA.add.
      }
      subst.




      steps. unfold hcall, ccall. steps.
      unfold body_to_tgt. unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)


      Transparent LinkedListStb ClientStb EchoStb MemStb. cbn in Heq. Opaque LinkedListStb ClientStb EchoStb MemStb. ss. clarify. rewrite Any.upcast_downcast. steps.
      unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
      force_l. eexists (x1 ⋅ x2, _). steps. force_l.
      { instantiate (1:= (x5 ⋅ x6 ⋅ x4)). admit "ez - pcm solver". }
      steps. force_l. eexists ε. steps. force_l. esplit.
      steps. force_l. { rewrite ! URA.unit_idl. refl. } steps.
      force_l. eexists tt. esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
      { esplits; try refl. }
      steps. force_l. { esplits; ss; try lia. } steps. clear_until _ASSUME0.
      gstep; econs; try apply Nat.lt_succ_diag_r; i; ss.
      { unfold alist_add. esplits; ss; eauto. eexists; iRefresh. left; iRefresh. iSplitL A; ss.
        - iApply A; ss.
        - iApply A0; ss.
      }
      exists 400. des. clarify. unfold alist_add; cbn. steps.
      des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'. steps.



      iDestruct SIM. destruct SIM as [SIM|SIM]; iRefresh; cycle 1.
      { exfalso. iMerge SIM _ASSUME0. rewrite <- own_sep in SIM. rewrite GRA.padding_add in SIM.
        iOwnWf SIM.
        { clear - _ASSUME1. admit "ez - pcm solver". }
        clear - WF. apply GRA.padding_wf in WF. des. ss.
      }
      iDestruct SIM. subst.
      assert(x0 = ns0).
      { iMerge SIM _ASSUME0. rewrite <- own_sep in SIM. rewrite GRA.padding_add in SIM.
        iOwnWf SIM.
        { clear - _ASSUME1. admit "ez - pcm solver". }
        eapply GRA.padding_wf in WF. des. eapply URA.auth_included in WF. des.
        clear - WF.
        Local Transparent URA.add.
        rr in WF. des. ss. des_ifs.
        Local Opaque URA.add.
      }
      subst.




      destruct (unint v) eqn:T; cycle 1.
      { steps. unfold triggerUB. steps. }
      destruct v; ss. clarify. steps.

      destruct (dec z (- 1)%Z).
      - subst. ss. steps.
        Transparent LinkedListStb ClientStb EchoStb MemStb. cbn in Heq. Opaque LinkedListStb ClientStb EchoStb MemStb. ss. clarify. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (x3 ⋅ x7, x5). steps. force_l. (*** x3 x7 ***)
        { eapply URA.extends_updatable. admit "ez - pcm solver". }
        steps. force_l. exists x5. steps. force_l. esplit. steps. force_l. { rewrite URA.unit_id. refl. } steps.
        force_l. eexists ns0. esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. }
        steps. force_l. { esplits; ss; try lia. } steps. clear_until _ASSUME0.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss.
        { exists (x3 ⋅ x7). unfold alist_add; ss. esplits; ss; eauto. exists ns0; iRefresh. left; iRefresh. iSplit SIM A; ss. }
        exists 400. des. clarify. unfold alist_add; cbn. steps.

        unfold unwrapN. des_ifs; cycle 1. { unfold triggerNB. steps. force_r; ss. } steps.
        force_l. esplit. force_l. eexists (_, _). iClears'. steps. force_l. { refl. } steps. force_l. esplit. force_l; ss.
        steps. force_l. esplit. force_l; et. steps.
        { iRefresh. iDestruct SIM0. esplits; eauto. eexists; iRefresh. eauto. }
      - steps.
        Transparent LinkedListStb ClientStb EchoStb MemStb. cbn in Heq. Opaque LinkedListStb ClientStb EchoStb MemStb. ss. clarify. rewrite Any.upcast_downcast. steps.
        force_l. eexists 1. steps. rewrite Any.upcast_downcast. ss. steps.

        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("push", [ll0; Vint z]↑). steps.
        Transparent LinkedListStb ClientStb EchoStb MemStb. cbn in Heq. Opaque LinkedListStb ClientStb EchoStb MemStb. ss. clarify. rewrite Any.upcast_downcast. steps.
        unfold HoareCall at 2, checkWf, forge, discard, put. steps. force_l. eexists (_, x3 ⋅ x7). steps. force_l.
        { rr in _ASSUME0. rr in SIM. instantiate (1:=(x5)). eapply URA.extends_updatable. admit "ez - pcm solver". }
        steps. force_l. eexists x7. steps. force_l. eexists x3. steps. force_l. { admit "ez - pcm solver". } steps.
        force_l. eexists (Vint z, List.map Vint ns0). steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. }
        steps. force_l. { esplits; ss; try lia. } steps.
        clear_until n.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss.
        { exists (x5). unfold alist_add; ss. esplits; ss; eauto. exists ns0; iRefresh. right; iRefresh; ss. }
        exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.
        do 2 iDestruct _ASSUME4. iPure A. apply Any.upcast_inj in A. des; clarify.
        iDestruct SIM0. destruct SIM0; iRefresh.
        { exfalso. iDestruct H1; subst. iMerge H1 SIM. rewrite <- own_sep in H1. rewrite GRA.padding_add in H1.
          iOwnWf H1.
          { clear - _ASSUME3. admit "ez - pcm solver". }
          clear - WF. apply GRA.padding_wf in WF. des. ss.
        }



        rename H1 into A. iMerge A SIM. rewrite <- own_sep in A. rewrite GRA.padding_add in A. rewrite URA.add_comm in A.
        assert(own_update: forall (x y: Σ) rx ctx, URA.updatable x y -> iHyp (Own x) rx -> URA.wf (rx ⋅ ctx) ->
                                                   exists ry, iHyp (Own y) ry /\ URA.wf (ry ⋅ ctx) /\ URA.updatable rx ry).
        { clear_until Σ. i. dup H. rr in H0. destruct H0; clear H0. subst. r in H.
          specialize (H (x0 ⋅ ctx)). rewrite ! URA.add_assoc in H. spc H.
          exists (y ⋅ x0). esplits; et.
          - rr. esplits; et.
          - eapply URA.updatable_add; try refl. et.
        }


        assert(x0 = ns0).
        { iOwnWf A.
          { clear - _ASSUME3. admit "ez - pcm solver". }
          eapply GRA.padding_wf in WF. des. eapply URA.auth_included in WF. des.
          clear - WF.
          Local Transparent URA.add.
          rr in WF. des. ss. des_ifs.
          Local Opaque URA.add.
        }
        subst.

        eapply own_update in A; cycle 1.
        { eapply GRA.padding_updatable. instantiate (1:= echo_black (z :: ns0) ⋅ echo_white (z :: ns0)).
          eapply URA.auth_update. rr. ii. des; ss. destruct ctx; ss; clarify.
        }
        { instantiate (1:= x9 ⋅ x10). admit "ez - pcm solver". }
        des. iRefresh.
        clear _ASSUME1 _ASSUME3.
        rewrite <- GRA.padding_add in A. rewrite own_sep in A. iDestruct A. subst.



        rewrite unfold_APC. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. force_l. eexists (x0 ⋅ x9, x11). steps. force_l.
        { rr in _ASSUME4. rr in A. rr in A2. clear - A1. rewrite ! URA.add_assoc.
          replace (mr ⋅ x3 ⋅ x9 ⋅ x10) with (mr ⋅ x3 ⋅ (x9 ⋅ x10)) by (rewrite ! URA.add_assoc; refl).
          replace (x0 ⋅ x9 ⋅ x11) with (x0 ⋅ x11 ⋅ x9); cycle 1.
          { rewrite <- ! URA.add_assoc. f_equal. rewrite URA.add_comm; ss. }
          eapply URA.updatable_add; et.
          eapply URA.extends_updatable. admit "ez - pcm solver". }
        steps. force_l. iExists A2. steps. force_l. esplit. steps. force_l. { rewrite URA.unit_id. refl. } steps.
        force_l. eexists (z :: ns0). steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. }
        steps. force_l. { esplits; ss; try lia. } steps.
        clear_until A2. iClears'.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss.
        { eexists (x0 ⋅ x9). unfold alist_add; ss. esplits; ss; eauto. exists (z :: ns0); iRefresh. left; iRefresh.
          iSplit A _ASSUME4; ss. }
        exists 400. des. clarify. unfold alist_add; cbn. steps.
        unfold unwrapN. des_ifs; cycle 1.
        { unfold triggerNB. ired. gstep; econsr; ss. (*** TODO: FIX TACTIC !]!!!!!!!!!!!!! ***) }
        steps. force_l. esplit. force_l. eexists (_, _). steps. force_l. { refl. } steps. force_l. esplits.
        force_l; ss. steps. force_l. esplits. force_l. { refl. } steps.
        { esplits; eauto. }
    }
    econs; ss.
    { init.
      unfold checkWf, forge, discard, put. steps.
      unfold echo_finishF, echo_finish_body. steps.
      iRefresh. do 2 iDestruct _ASSUME0. iPure A. iPure A0. clarify.
      iDestruct SIM.
      destruct SIM as [A|A]; iRefresh; cycle 1.
      { exfalso. iMerge A _ASSUME0. rewrite <- own_sep in A. rewrite GRA.padding_add in A.
        iOwnWf A.
        { clear - _ASSUME. admit "ez - pcm solver". }
        clear - WF. apply GRA.padding_wf in WF. des. ss.
      }



      iDestruct A. subst.
      rename x into ns. rename x0 into ns0.
      assert(ns = ns0).
      { iMerge A _ASSUME0. rewrite <- own_sep in A. rewrite GRA.padding_add in A.
        iOwnWf A.
        { clear - _ASSUME. admit "ez - pcm solver". }
        eapply GRA.padding_wf in WF. des. eapply URA.auth_included in WF. des.
        clear - WF.
        Local Transparent URA.add.
        rr in WF. des. ss. des_ifs.
        Local Opaque URA.add.
      }
      subst.




      steps. unfold hcall, ccall. steps.
      unfold body_to_tgt. unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)

      destruct ns0; ss.
      - steps. rewrite Any.upcast_downcast. ss. steps.
        rewrite unfold_is_list in A0. iPure A0. subst. ss. steps.
        force_l. esplit. force_l. eexists (_, _). steps. force_l. { refl. } steps. force_l. esplit. force_l; ss. steps.
        force_l. esplit. force_l. { refl. } steps.
        { unfold alist_add. esplits; ss; eauto. eexists; iRefresh. left; iRefresh. instantiate (1:=[]). ss. iSplitL A; ss. }
      - steps. rewrite Any.upcast_downcast. ss. steps.
        force_l. eexists 3. steps.

        Transparent LinkedListStb ClientStb EchoStb MemStb. cbn in Heq, Heq0. Opaque LinkedListStb ClientStb EchoStb MemStb. ss. clarify.
        rewrite ! Any.upcast_downcast. steps.

        assert(T: is_zero ll = false).
        { rewrite unfold_is_list in *. do 4 iDestruct A0. iPure A0. subst. ss. }
        rewrite T. clear T.
        steps.


        (* rr in A0. rr in A. rr in _ASSUME0. *)
        (*** x2 x1 x5 ***)

        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("alloc", [Vint 1]↑). steps.
        Transparent LinkedListStb ClientStb EchoStb MemStb. cbn in Heq. Opaque LinkedListStb ClientStb EchoStb MemStb. ss. clarify. rewrite Any.upcast_downcast. steps.
        unfold HoareCall at 3, checkWf, forge, discard, put. steps. force_l. eexists (x5, x2 ⋅ x1). steps. force_l.
        { rewrite URA.unit_idl. eapply URA.extends_updatable. admit "ez - pcm solver". }
        steps. force_l. eexists ε. steps. force_l. eexists _. steps. force_l. { rewrite URA.unit_idl. refl. } steps.
        force_l. eexists 1. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. esplits; ss. }
        steps. force_l. { esplits; ss; try lia. } steps.
        clear_until _ASSUME0.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss.
        { unfold alist_add; ss. esplits; ss; eauto. exists (z :: ns0); iRefresh. right; iRefresh; ss. }
        exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.

        do 2 iDestruct _ASSUME2. iPure _ASSUME2. subst. apply Any.upcast_inj in _ASSUME2. des; clarify.
        iDestruct SIM. destruct SIM as [B|B]; iRefresh.
        { exfalso. iDestruct B; subst. iMerge B A. rewrite <- own_sep in B. rewrite GRA.padding_add in B.
          iOwnWf B.
          { clear - _ASSUME1. admit "ez - pcm solver". }
          clear - WF. apply GRA.padding_wf in WF. des. ss.
        }
        assert(x = z :: ns0).
        { iMerge A B. rewrite <- own_sep in A. rewrite GRA.padding_add in A.
          iOwnWf A.
          { clear - _ASSUME1. admit "ez - pcm solver". }
          eapply GRA.padding_wf in WF. des. eapply URA.auth_included in WF. des.
          clear - WF.
          Local Transparent URA.add.
          rr in WF. des. ss. des_ifs.
          Local Opaque URA.add.
        }
        subst.
        steps.










        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("pop2", [ll; Vptr x0 0]↑). steps.
        Transparent LinkedListStb ClientStb EchoStb MemStb. cbn in Heq. Opaque LinkedListStb ClientStb EchoStb MemStb. ss. clarify. rewrite Any.upcast_downcast. steps.
        unfold HoareCall at 3, checkWf, forge, discard, put. steps. force_l. eexists (mr, x1 ⋅ x2 ⋅ x3 ⋅ x7). steps. force_l.
        { eapply URA.extends_updatable. admit "ez - pcm solver". }
        steps. force_l. exists (x2 ⋅ x7). steps. force_l. eexists _. steps. force_l. { instantiate (1:= x1 ⋅ x3). admit "ez - pcm solver". } steps.
        force_l. eexists (List.map Vint (z :: ns0), x0). steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplit A0 A1; ss.
          - iSplitP; ss.
          - eexists; iRefresh. iApply A1; ss. }
        steps. force_l. { esplits; ss; try lia. } steps.
        clear_until A.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss.
        { unfold alist_add; ss. esplits; ss; eauto. exists (z :: ns0); iRefresh. right; iRefresh; ss. }
        exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.
        admit "TODO~~~~~~~~~~~~".
    }
  Unshelve.
    all: ss.
    all: try (by repeat econs; et).
  Qed.

End SIMMODSEM.


