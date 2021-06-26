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
Require Import Mem1 MemOpen STB.

Set Implicit Arguments.

Local Open Scope nat_scope.




Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  From iris.algebra Require Import big_op.
  From iris.bi Require Import big_op.

  Let wf: _ -> W -> Prop :=
    @mk_wf _ unit
           (fun _ _stk_mgr0 _ =>
              ⌜True⌝ ** (∃ (stk_mgr0: gmap mblock (list val)),
                            (⌜_stk_mgr0 = stk_mgr0↑⌝) ∧
                            ({{"SIM": ([∗ map] handle ↦ stk ∈ stk_mgr0,
                                       (∃ hd, OwnM ((handle, 0%Z) |-> [hd]) ** is_list hd stk))}})
                        ))
           (* (fun _ _ _ => ⌜True⌝%I) *)
           top4
  .

  Variable global_stb: gname -> option fspec.
  Hypothesis STBINCL: stb_incl (to_stb (StackStb ++ MemStb)) global_stb.

  Ltac renamer :=
    match goal with
    | [mp_src: gmap nat (list val) |- _ ] =>
      let tmp := fresh "_tmp_" in
      rename mp_src into tmp;
      let name := fresh "stk_mgr0" in
      rename tmp into name
    end;
    match goal with
    | [ACC: current_iPropL _ ?Hns |- _ ] =>
      match Hns with
      | context[(?name, ([∗ map] _↦_ ∈ _, _))%I] => mRename name into "SIM"
      end
    end
  .

  Theorem sim_modsem: ModSemPair.sim (NewStack1.StackSem global_stb) NewStack0.StackSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. econs; ss. eapply to_semantic. iIntros "H". iClear "H". iSplits; ss. }
    econs; ss.
    { unfold newF. trivial_init. fold wf. mDesAll; des; subst. ss.
      unfold new_body, KModSem.transl_fun_tgt, ccall, cfun. steps.

      kstart 2.
      kcatch. { eapply STBINCL. stb_tac; ss. } hcall _ (Some _) _ with "SIM"; ss; et.
      { iModIntro. iSplits; ss; et.
        { instantiate (1:=1%nat). ss. }
        { iPureIntro. unfold_modrange_64. ss. }
      }
      { ss. }
      Ltac post_call :=
        fold wf; clear_fast; mDesAll; des_safe; subst; try rewrite Any.upcast_downcast in *; clarify; renamer.
      post_call. rename a0 into handle.
      steps.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall _ (Some (_, _, _)) _ with "SIM A"; ss; et.
      { iModIntro. iSplitL "SIM"; ss.
        { iSplits; ss; et. }
        { iSplits; ss; et. }
      }
      { ss. }
      post_call. steps. eapply Any.downcast_upcast in _UNWRAPN0. des. clarify.
      kstop. steps.

      force_l. exists handle. steps. rewrite Any.upcast_downcast. steps.
      destruct (stk_mgr0 !! handle) eqn:T.
      { mAssertPure False; ss.
        (*** IEXPLOIT*) iDestruct (big_sepM_lookup_acc with "SIM") as "[B C]"; et. iDestruct "B" as (x) "[B D]".
        iApply (points_to_disj with "POST B"); et.
      }
      force_l; ss. steps.

      hret _; ss.
      { iModIntro. iSplits; ss; et. iApply big_sepM_insert; ss. iFrame; ss; et. }
      (*** ISPECIALIZE SYNTAX: iSpecialize ("A" $! _ _ H0). et. *)
    }
    econs; ss.
    { unfold popF. trivial_init. fold wf. mDesAll; des; subst. ss.
      unfold pop_body, KModSem.transl_fun_tgt, ccall, cfun. steps.

      rewrite Any.upcast_downcast in *. steps. kstart 7.

      hide_k. destruct v; ss. des_ifs. clear_fast.
      renamer. rename n into handle. rename l into stk. rename _UNWRAPU0 into T.
      mAssert _ with "SIM".
      { iDestruct (big_sepM_delete with "SIM") as "[B C]"; et. (* big_sepM_lookup_acc *)
        instantiate (1:=_ ** _). iSplitL "B". { iExact "B". } iExact "C". }
      mDesAll; ss. rename a into hd. renamer.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall _ (Some (_, _, _)) _ with "SIM A"; ss; et.
      { iModIntro. iSplitL "SIM"; ss; et. iSplits; ss; et. }
      { ss. }
      post_call. unhide_k. steps. rewrite Any.upcast_downcast in *. clarify.
      hide_k.

      destruct stk as [|x stk1]; ss.
      - mDesAll. subst.
        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "SIM POST"; ss.
        { iModIntro. iSplitL "SIM"; ss; [et|]. iSplits; ss. repeat iRight. et. }
        post_call. unhide_k. steps. rewrite Any.upcast_downcast in *. clarify.
        hide_k. ss. steps. unhide_k. kstop. steps.
        rewrite Any.upcast_downcast. steps.

        hret _; ss. iModIntro. iSplits; ss; et.
        destruct (stk_mgr1 !! handle) eqn:U.
        { iExFalso. iDestruct (big_sepM_lookup_acc with "SIM") as "[B C]"; et. iDestruct "B" as (x) "[SIM B]".
          iApply (points_to_disj with "POST1 SIM"). }
        iApply big_sepM_insert; ss. iSplitR "SIM"; et.
      - mDesAll. subst. rename a into hd. rename a0 into tl. rewrite points_to_split in ACC. mDesOwn "A1".
        rewrite Z.add_0_l in *.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "SIM A1"; ss.
        { iModIntro. iSplitL "SIM"; ss. { et. } iSplits; ss; et. }
        post_call. unhide_k. steps. rewrite Any.upcast_downcast in *. clarify. steps.

        unfold scale_int. uo. steps.
        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "SIM POST1"; ss.
        { iModIntro. iSplitL "SIM"; ss; et. iSplits; ss; et. }
        post_call. steps.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "SIM A2"; ss.
        { iModIntro. iSplitL "SIM"; ss; et. iSplits; ss; et. }
        post_call. steps.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "SIM POST2"; ss.
        { iModIntro. iSplitL "SIM"; ss; et. iSplits; ss; et. }
        post_call. steps.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "SIM POST1"; ss.
        { iModIntro. iSplitL "SIM"; ss; et. iSplits; ss; et. }
        post_call. steps.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "SIM POST"; ss.
        { iModIntro. iSplitL "SIM"; ss; et. iSplits; ss; et. }
        post_call. steps.

        kstop. steps. rewrite Any.upcast_downcast. steps. renamer.

        destruct (stk_mgr1 !! handle) eqn:V.
        { mAssertPure False; ss. iDestruct (big_sepM_lookup_acc with "SIM") as "[B C]"; et.
          iDestruct "B" as (y) "[SIM B]".
          iApply (points_to_disj with "POST1 SIM"). }

        hret _; ss.
        { iModIntro. iSplits; ss; et. iApply big_sepM_insert; ss. iFrame. iExists _; ss. iFrame. }
    }
    econs; ss.
    { unfold pushF. trivial_init. fold wf. mDesAll; des; subst. ss.
      unfold push_body, KModSem.transl_fun_tgt, ccall, cfun. steps.

      rewrite Any.upcast_downcast in *; clarify. steps. kstart 7.

      hide_k. destruct v; ss. des_ifs. clear_tac.
      rename n into handle. renamer. rename l into stk. rename _UNWRAPU into T.
      mAssert _ with "SIM".
      { iDestruct (big_sepM_delete with "SIM") as "[B C]"; et. (* big_sepM_lookup_acc *)
        instantiate (1:=_ ** _). iSplitL "B". { iExact "B". } iExact "C". }
      mDesAll; ss. renamer. rename a into hd.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some _) _ with "SIM"; ss; et.
      { iModIntro. iSplitL "SIM"; et. iSplits; ss; et.
        { instantiate (1:=2). ss. }
        { iPureIntro. ss. }
      }
      post_call. rename a0 into node. unhide_k. steps. rewrite Any.upcast_downcast in *. clarify. steps.

      rewrite points_to_split in ACC. mDesOwn "A1". rewrite Z.add_0_l in *. clear_fast.

      unfold scale_int. uo. steps.
      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "A SIM"; ss; et.
      { iModIntro. iSplitL "SIM"; et. iSplits; ss; et. }
      post_call. steps.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "A1 SIM"; ss; et.
      { iModIntro. iSplitL "SIM"; et. iSplits; ss; et. }
      post_call. steps.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "A3 SIM"; ss; et.
      { iModIntro. iSplitL "SIM"; et. iSplits; ss; et. }
      post_call. steps.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "POST SIM"; ss; et.
      { iModIntro. iSplitL "SIM"; et. iSplits; ss; et. }
      post_call. steps.

      kstop. steps. rewrite Any.upcast_downcast. steps.

      destruct (stk_mgr1 !! handle) eqn:V.
      { mAssertPure False; ss. iDestruct (big_sepM_lookup_acc with "SIM") as "[B C]"; et.
        iDestruct "B" as (y) "[SIM B]". iApply (points_to_disj with "POST3 SIM"). }

      hret _; ss.
      { iModIntro. iSplits; ss; et.
        iApply big_sepM_insert; ss. iFrame. iExists _; ss. iFrame.
        iExists _, _. iFrame. iSplit; ss. erewrite points_to_split with (hd:=v0) (tl:=[hd]).
        iSplitL "POST1"; et.
      }
    }
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk, stb_incl (to_stb (StackStb ++ MemStb)) (global_stb sk).

  Theorem correct: ModPair.sim (NewStack1.Stack global_stb) NewStack0.Stack.
  Proof.
    econs; ss. ii. eapply sim_modsem; ss.
  Qed.

End SIMMOD.
