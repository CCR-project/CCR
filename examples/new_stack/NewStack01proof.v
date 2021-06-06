Require Import NewStack0 NewStack1 HoareDef SimModSem.
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
Require Import TODOYJ.
Require Import HTactics Logic IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB TODO.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section AUX.

  Context `{Σ: GRA.t}.

  Lemma APCK_start_clo
        (at_most: Ord.t) (n1: Ord.t)
        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (ATMOST: (at_most < kappa)%ord)
        (FUEL: (n1 + 5 < n0)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                       (mr_src0, mp_src0, fr_src0,
                       (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK at_most))) >>= k_src)
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt APCK)) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    unfold APCK. steps. force_l.
    exists at_most. ired_l.  _step; [by eauto with ord_step|]. steps; [by eauto with ord_step|].
    unfold guarantee. ired_both. force_l. esplits; et.
    ired_both. _step; [by eauto with ord_step|]. steps; [by eauto with ord_step|]. ss.
    guclo lordC_spec. econs; et. rewrite OrdArith.add_O_r. refl.
  Qed.

  Lemma APCK_step_clo
        (fn: gname) (next: Ord.t) (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (FUEL: (n1 + 11 < n0)%ord)
        (ftsp: ftspec unit unit)
        (FIND: alist_find fn stb = Some (KModSem.disclose ftsp))
        (NEXT: (next < at_most)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                      (mr_src0, mp_src0, fr_src0,
                       (HoareCall true o (KModSem.disclose ftsp) fn (inl tt));;;
                                 tau;; tau;; (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK next)))
                                               >>= k_src)
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
             (mr_src0, mp_src0, fr_src0, (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK at_most)))
                                           >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APCK. steps. force_l. exists false. ired_both.
    _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l. esplits; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l. esplits; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    rewrite FIND. ired_both. rewrite Any.upcast_downcast. ired_both.
    guclo lordC_spec. econs; et. { rewrite OrdArith.add_O_r. refl. }
    match goal with
    | [SIM: gpaco6 _ _ _ _ _ _ _ _ ?i0 _ |- gpaco6 _ _ _ _ _ _ _ _ ?i1 _] =>
      replace i1 with i0; auto
    end.
    f_equal. grind. ired_both. grind. ired_both. grind.
  Qed.

  Lemma APCK_stop_clo
        (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (FUEL: (n1 + 2 < n0)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                      (mr_src0, mp_src0, fr_src0, k_src ())
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK at_most))) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APCK. steps. force_l. exists true.
    ired_both; _step; [by eauto with ord_step|].
    ired_both; _step; [by eauto with ord_step|].
    steps.
    guclo lordC_spec. econs; et. { rewrite OrdArith.add_O_r. refl. }
  Qed.

End AUX.

Ltac kstart _at_most :=
  eapply (APCK_start_clo) with (at_most := _at_most);
  [eauto with ord_kappa|
   (try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
  ]
.

Ltac kstep _fn :=
  eapply (@APCK_step_clo _ _fn);
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
   (try by (stb_tac; refl))|
   (eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r)|
  ].

Ltac kcatch :=
  match goal with
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn _) >>= _)) ] =>
    kstep fn
  end.

Ltac kstop :=
  eapply APCK_stop_clo;
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|].





Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  (*** TODO: remove redundancy with Stack1.v ***)
  Fixpoint is_list (ll: val) (xs: list val): iProp :=
    match xs with
    | [] => (⌜ll = Vnullptr⌝: iProp)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl]))
                             ** is_list ltl xtl: iProp)%I
    end
  .

  From iris.algebra Require Import big_op.
  From iris.bi Require Import big_op.

  (*** TODO: How about supporting "pattern" on x? Ask Iris people ***)
  (* Notation "'[∗' 'list]' x ∈ l , P" := *)
  (*   (big_opL bi_sep (λ _ x, P%I) l) : bi_scope. *)

  Let wf: W -> Prop :=
    @mk_wf _ unit
           (fun _ _stk_mgr0 _ =>
              ⌜True⌝ ** (∃ (stk_mgr0: gmap mblock (list Z)),
                            (⌜<<CAST: _stk_mgr0 = stk_mgr0↑>>⌝) ∧
                            ([∗ map] handle ↦ stk ∈ stk_mgr0,
                             (∃ hd, OwnM ((handle, 0%Z) |-> [hd]) ** is_list hd (map Vint stk))))%I)
           (fun _ _ _ => ⌜True⌝%I)
  .

  (*** TODO: remove redundancy with Mem0OpenProof ***)
  Definition __hide_mark A (a : A) : A := a.
  Lemma intro_hide_mark: forall A (a: A), a = __hide_mark a. refl. Qed.

  Ltac hide_k := 
    match goal with
    | [ |- (gpaco6 _ _ _ _ _ _ _ _ (_, ?isrc >>= ?ksrc) (_, ?itgt >>= ?ktgt)) ] =>
      erewrite intro_hide_mark with (a:=ksrc);
      erewrite intro_hide_mark with (a:=ktgt);
      let name0 := fresh "__KSRC__" in set (__hide_mark ksrc) as name0; move name0 at top;
      let name0 := fresh "__KTGT__" in set (__hide_mark ktgt) as name0; move name0 at top
    end.

  Ltac unhide_k :=
    do 2 match goal with
    | [ H := __hide_mark _ |- _ ] => subst H
    end;
    rewrite <- ! intro_hide_mark
  .

  Ltac mRename A B :=
    match goal with
    | [H: current_iPropL _ ?iprops |- _ ] =>
      match iprops with
      | context[(A, ?x)] => mAssert x with A as B; [iApply A|]
      end
    end.
  Ltac mRefresh := on_current ltac:(fun H => move H at bottom).

  (*** TODO: move to Mem1.v ***)
  Lemma points_to_disj
        ptr x0 x1
    :
      (OwnM (ptr |-> [x0]) -∗ OwnM (ptr |-> [x1]) -* ⌜False⌝)
  .
  Proof.
    destruct ptr as [blk ofs].
    iIntros "A B". iCombine "A B" as "A". iOwnWf "A" as WF0.
    unfold points_to in WF0. rewrite ! unfold_points_to in *. repeat (ur in WF0); ss.
    specialize (WF0 blk ofs). des_ifs; bsimpl; des; des_sumbool; zsimpl; ss; try lia.
  Qed.

  Variable global_stb: list (string * fspec).
  Hypothesis STBINCL: stb_incl (DebugStb ++ StackStb ++ MemStb) global_stb.

  Theorem sim_modsem: ModSemPair.sim (NewStack1.StackSem global_stb) NewStack0.StackSem.
  Proof.
    econstructor 1 with (wf:=wf); ss; et; swap 2 3.
    { econs; ss.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iClear "H". iSplit; ss.
        iExists _. iSplit; ss.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iPureIntro. ss.
    }
    econs; ss.
    { unfold newF. init. harg. destruct varg_src.
      { ss. des_ifs; mDesAll; ss. }
      destruct x; mDesAll; ss. des; subst.
      unfold new_body, ccall. steps. rewrite Any.upcast_downcast in *; clarify. steps. kstart 1.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall _ (Some _) _ with "A1"; ss; et.
      { iModIntro. iSplitL; ss; et. iPureIntro. esplits; et. instantiate (1:=1%nat). ss. }
      { ss. }
      steps. mDesAll; des; clarify. rewrite Any.upcast_downcast in *. clarify. kstop. steps.
      rename a3 into handle. force_l. exists handle. steps. rewrite Any.upcast_downcast. steps.
      rename a2 into stk_mgr0. destruct (stk_mgr0 !! handle) eqn:T.
      { mAssertPure False; ss.
        (*** IEXPLOIT*) iDestruct (big_sepM_lookup_acc with "A1") as "[B C]"; et. iDestruct "B" as (x) "[A1 B]".
        iApply (points_to_disj with "A A1"); et.
      }
      force_l; ss. steps.

      hret _; ss.
      { iModIntro. iSplitL; ss. iSplit; ss. iExists _. iSplit; ss.
        iApply big_sepM_insert; ss. iFrame; ss; et.
        (*** ISPECIALIZE SYNTAX: iSpecialize ("A" $! _ _ H0). et. *)
      }
    }
    econs; ss.
    { unfold popF. init. harg. destruct varg_src.
      { ss. des_ifs; mDesAll; ss. }
      destruct x; mDesAll; ss. des; subst.
      unfold pop_body, ccall. steps. rewrite Any.upcast_downcast in *; clarify. steps. kstart 7.

      hide_k. destruct v; ss. des_ifs.
      rename n into handle. rename a0 into stk_mgr0. rename l into stk. rename _UNWRAPU0 into T.
      mAssert _ with "A1".
      { iDestruct (big_sepM_delete with "A1") as "[B C]"; et. (* big_sepM_lookup_acc *)
        instantiate (1:=_ ** _). iSplitL "B". { iExact "B". } iExact "C". }
      mDesAll; ss. rename a0 into hd. mRename "A1" "INV".

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall _ (Some (_, _, _)) _ with "INV A"; ss; et.
      { iModIntro. iFrame; ss; et. }
      { ss. }
      steps. mDesAll. des; clarify. unhide_k. steps. rewrite Any.upcast_downcast in *. clarify.
      hide_k. rename a0 into stk_mgr1. mRename "A1" "INV".

      destruct stk as [|x stk1]; ss.
      - mDesAll. subst.
        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "INV POST"; ss.
        { iModIntro. iSplitL "INV"; ss. { et. } iSplit; ss. iSplit; ss. iSplit; ss. repeat iRight. et. }
        steps. mDesAll. des; clarify. unhide_k. steps. rewrite Any.upcast_downcast in *. clarify.
        hide_k. rename a2 into stk_mgr2. des_u. ss. steps. unhide_k. kstop. steps.
        rewrite Any.upcast_downcast. steps. mRename "A1" "INV".

        hret _; ss. iModIntro. iSplitL; ss. iSplit; ss. iExists _. iSplit; ss.
        destruct (stk_mgr2 !! handle) eqn:U.
        { iExFalso. iDestruct (big_sepM_lookup_acc with "INV") as "[B C]"; et. iDestruct "B" as (x) "[INV B]".
          iApply (points_to_disj with "POST1 INV"). }
        iApply big_sepM_insert; ss. iSplitR "INV"; et.
      - mDesAll. subst. rename a0 into hd. rename a2 into tl. rewrite points_to_split in ACC. mDesOwn "A1".
        rewrite Z.add_0_l in *.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "INV A1"; ss.
        { iModIntro. iSplitL "INV"; ss. { et. } iSplit; ss. iSplit; ss. iSplit; ss. iLeft; et. }
        mDesAll; des; subst. des_u; ss. rename a2 into stk_mgr2. steps. unhide_k.
        rewrite Any.upcast_downcast. steps. mRename "A3" "INV".

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "INV POST1"; ss.
        { iModIntro. iSplitL "INV"; ss; et. }
        steps. mDesAll. des; subst. mRename "A3" "INV". rewrite Any.upcast_downcast in *. clarify.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "INV A2"; ss.
        { iModIntro. iSplitL "INV"; ss; et. }
        steps. mDesAll. des; subst. mRename "A2" "INV". rewrite Any.upcast_downcast in *. clarify.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "INV POST2"; ss.
        { iModIntro. iSplitL "INV"; ss; et. }
        steps. mDesAll. des; subst. mRename "A2" "INV".

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "INV POST1"; ss.
        { iModIntro. iSplitL "INV"; ss; et. }
        steps. mDesAll. des; subst. mRename "A2" "INV".

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "INV POST"; ss.
        { iModIntro. iSplitL "INV"; ss; et. }
        steps. mDesAll. des; subst. mRename "A2" "INV".

        kstop. steps. rewrite Any.upcast_downcast. steps. rename a10 into stk_mgr3.
        destruct (alist_find "debug" (DebugStb ++ StackStb ++ MemStb)) eqn:U; cycle 1.
        { exfalso. stb_tac. ss. }
        dup U. revert U. stb_tac. clarify. i.
        apply STBINCL in U. rewrite U. steps. rewrite Any.upcast_downcast. steps.

        destruct (stk_mgr3 !! handle) eqn:V.
        { mAssertPure False; ss. iDestruct (big_sepM_lookup_acc with "INV") as "[B C]"; et.
          iDestruct "B" as (y) "[INV B]".
          iApply (points_to_disj with "POST1 INV"). }

        hcall _ _ _ with "INV POST1 A"; ss; et.
        { iModIntro. iSplitL; ss; et.
          - iSplit; ss. iExists _; ss. iSplit; ss. iApply big_sepM_insert; ss. iFrame. iExists _; ss. iFrame.
          - iPureIntro. esplits; et. rewrite Any.upcast_downcast; ss. }
        { ss. }
        steps.

        hret _; ss. iModIntro. iSplitL; ss.
    }
    econs; ss.
    {
      admit "ez - TODO".
    }
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Variable global_stb: Sk.t -> list (string * fspec).
  Hypothesis STBINCL: forall sk, stb_incl (DebugStb ++ StackStb ++ MemStb) (global_stb sk).

  Theorem correct: ModPair.sim (NewStack1.Stack global_stb) NewStack0.Stack.
  Proof.
    econs; ss.
    { ii. eapply adequacy_lift. eapply sim_modsem; ss. }
    ii; ss. repeat (Psimpl; econs; ss).
  Qed.

End SIMMOD.
