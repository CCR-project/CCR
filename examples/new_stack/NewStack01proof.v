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



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

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
      mDesAll; ss. rename a0 into hd. mRename "A1" into "INV".

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall _ (Some (_, _, _)) _ with "INV A"; ss; et.
      { iModIntro. iFrame; ss; et. }
      { ss. }
      steps. mDesAll. des; clarify. unhide_k. steps. rewrite Any.upcast_downcast in *. clarify.
      hide_k. rename a0 into stk_mgr1. mRename "A1" into "INV".

      destruct stk as [|x stk1]; ss.
      - mDesAll. subst.
        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "INV POST"; ss.
        { iModIntro. iSplitL "INV"; ss. { et. } iSplit; ss. iSplit; ss. iSplit; ss. repeat iRight. et. }
        steps. mDesAll. des; clarify. unhide_k. steps. rewrite Any.upcast_downcast in *. clarify.
        hide_k. rename a2 into stk_mgr2. des_u. ss. steps. unhide_k. kstop. steps.
        rewrite Any.upcast_downcast. steps. mRename "A1" into "INV".

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
        rewrite Any.upcast_downcast. steps. mRename "A3" into "INV".

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "INV POST1"; ss.
        { iModIntro. iSplitL "INV"; ss; et. }
        steps. mDesAll. des; subst. mRename "A3" into "INV". rewrite Any.upcast_downcast in *. clarify.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "INV A2"; ss.
        { iModIntro. iSplitL "INV"; ss; et. }
        steps. mDesAll. des; subst. mRename "A2" into "INV". rewrite Any.upcast_downcast in *. clarify.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "INV POST2"; ss.
        { iModIntro. iSplitL "INV"; ss; et. }
        steps. mDesAll. des; subst. mRename "A2" into "INV".

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "INV POST1"; ss.
        { iModIntro. iSplitL "INV"; ss; et. }
        steps. mDesAll. des; subst. mRename "A2" into "INV".

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "INV POST"; ss.
        { iModIntro. iSplitL "INV"; ss; et. }
        steps. mDesAll. des; subst. mRename "A2" into "INV".

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
    { unfold pushF. init. harg. destruct varg_src.
      { ss. des_ifs; mDesAll; ss. }
      destruct x; mDesAll; ss. des; subst.
      unfold push_body, ccall. steps. rewrite Any.upcast_downcast in *; clarify. steps. kstart 7.

      hide_k. destruct v, v0; ss. des_ifs. des_u. clear_tac.
      rename n into handle. rename a0 into stk_mgr0. rename l into stk. rename _UNWRAPU into T.
      mAssert _ with "A1".
      { iDestruct (big_sepM_delete with "A1") as "[B C]"; et. (* big_sepM_lookup_acc *)
        instantiate (1:=_ ** _). iSplitL "B". { iExact "B". } iExact "C". }
      mDesAll; ss. rename a into hd. mRename "A1" into "INV".

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some _) _ with "INV"; ss; et.
      { iModIntro. iSplitL "INV"; et. iSplit; ss; et. iSplit; ss; et. instantiate (1:=2). ss. }
      steps. mDesAll. des; clarify. unhide_k. steps. rewrite Any.upcast_downcast in *. clarify.
      rename a into stk_mgr1. rename a0 into node. mRename "A3" into "INV". steps.
      rewrite points_to_split in ACC. mDesOwn "A1". rewrite Z.add_0_l in *.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "A INV"; ss; et.
      { iModIntro. iSplitL "INV"; et. }
      steps. mDesAll. des; clarify. rename a into stk_mgr2. des_u. mRename "A4" into "INV".

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "A1 INV"; ss; et.
      { iModIntro. iSplitL "INV"; et. }
      steps. mDesAll. des; clarify. rename a into stk_mgr3. des_u. mRename "A1" into "INV".
      rewrite Any.upcast_downcast in *. clarify.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "A3 INV"; ss; et.
      { iModIntro. iSplitL "INV"; et. }
      steps. mDesAll. des; clarify. clear_tac. rename a into stk_mgr1. mRename "A1" into "INV".

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "POST INV"; ss; et.
      { iModIntro. iSplitL "INV"; et. }
      steps. mDesAll. des; clarify. clear_tac. rename a into stk_mgr1. mRename "A1" into "INV". kstop. steps.
      rewrite Any.upcast_downcast. steps.

      destruct (alist_find "debug" (DebugStb ++ StackStb ++ MemStb)) eqn:U; cycle 1.
      { exfalso. stb_tac. ss. }
      dup U. revert U. stb_tac. clarify. i.
      apply STBINCL in U. rewrite U. steps. rewrite Any.upcast_downcast. steps.

      destruct (stk_mgr1 !! handle) eqn:V.
      { mAssertPure False; ss. iDestruct (big_sepM_lookup_acc with "INV") as "[B C]"; et.
        iDestruct "B" as (y) "[INV B]". iApply (points_to_disj with "POST3 INV"). }

      hcall _ _ _ with "-"; ss; et.
      { iModIntro. iSplitL; ss; et.
        - iSplit; ss. iExists _; ss. iSplit; ss. iApply big_sepM_insert; ss. iFrame. iExists _; ss. iFrame.
          iExists _, _. iFrame. iSplit; ss. erewrite points_to_split with (hd:=Vint z) (tl:=[v]).
          iSplitL "POST1"; et.
        - iPureIntro. esplits; et. rewrite Any.upcast_downcast; ss. }
      { ss. }
      steps.

      hret _; ss. iModIntro. iSplitL; ss.
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
