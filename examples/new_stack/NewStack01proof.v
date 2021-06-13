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

  (*** TODO: move to proper place ***)
  Definition iNW (name: string) (P: iProp'): iProp' := P.
  Hint Unfold iNW.
  Notation "'<<' x ';' t '>>'" := (iNW x t) (at level 80, no associativity).

  Lemma trivial_init_clo
        A
        (R_src: A -> Any.t -> Any.t -> iProp) (R_tgt: A -> Any.t -> Any.t -> iProp)
        fn f_tgt gstb body
        (POST: forall a mp_src mp_tgt mr_src mr_tgt fr_src ctx varg
                      (RTGT: R_tgt a mp_src mp_tgt mr_tgt)
                      (ACC: current_iPropL ctx [("INV", R_src a mp_src mp_tgt)])
          ,
            gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) bot6 bot6
                   _ _
                   (fun _ _ => eq)
                   89
                   (((mr_src, mp_src), fr_src),
                    ((interp_hCallE_tgt gstb ord_top (KModSem.transl_fun_tgt body varg) ctx)
                      >>= (HoareFunRet (fun (_: unit) (reth retl: Any.t) => (⌜reth = retl⌝%I): iProp) tt))
                   )
                   (((mr_tgt, mp_tgt), ε), (f_tgt varg))
        )
    :
      sim_fnsem (mk_wf R_src R_tgt) (fn, fun_to_tgt gstb (mk_kspecbody fspec_trivial body body)) (fn, f_tgt)
  .
  Proof.
    init. harg. rename a into aa.
    Ltac dull_tac :=
      match goal with
      | ord_cur: ord |- _ =>
        assert(ord_cur = ord_top) by (on_current ltac:(fun ACC => clear - ACC); mClear "INV";
                                      des_ifs; mDesAll; des; ss);
        subst
      end;
      match goal with
      | |- context[map_or_else (Any.split ?v) ?l (KModSem.transl_fun_tgt ?body ?varg_src)] =>
        let r := constr:(KModSem.transl_fun_tgt body varg_src) in
        let varg := match goal with | [H: context[varg_src = ?varg] |- _] => varg end in
        replace (map_or_else (Any.split v) l r) with (KModSem.transl_fun_tgt body varg);
        [|on_current ltac:(fun ACC => clear - ACC); mClear "INV"; des_ifs; mDesAll; ss; des; subst; ss; fail]
      end;
      mClear "PRE"; rename x into _unused.
    dull_tac.
    exploit POST; et. intro SIM.
    match goal with
    | [SIM: gpaco6 _ _ _ _ _ _ _ _ ?i0 _ |- gpaco6 _ _ _ _ _ _ _ _ ?i1 _] =>
      replace i1 with i0; eauto
    end.
    repeat f_equal. Local Transparent HoareFunRet. unfold HoareFunRet. Local Opaque HoareFunRet.
    extensionality x. des_ifs. grind. rewrite map_or_else_same. ss.
  Qed.

  Ltac trivial_init := eapply trivial_init_clo; i; des_u.

  Ltac clear_fast :=
    repeat multimatch goal with
           | a:unit |- _ => destruct a
           | H:True |- _ => clear H
           | H:(True)%I _ |- _ => clear H
           | H: _ |- _ =>
             (*** unused definitions ***)
             tryif (is_prop H)
             then idtac
             else clear H
           end
  .

  Ltac iSplits :=
    intros; unfold NW, iNW;
    repeat match goal with
           | [ |- @ex _ _ ] => eexists
           | [ |- _ /\ _ ] => split
           | [ |- @sig _ _ ] => eexists
           | [ |- @sigT _ _ ] => eexists
           | [ |- @prod _  _ ] => split
           | |- environments.envs_entails _ (@bi_exist _ _ _) => iExists _
           | _ => iSplit
           end
  .

  Ltac mDes' l :=
    match l with
    | [] => idtac
    | (?Hn, ?P) :: ?tl =>
      match P with
      | @bi_pure _ _ => mPure Hn
      | @bi_exist _ _ _ => mDesEx Hn
      | @bi_sep _ _ _ => mDesSep Hn
      | @bi_and _ _ (@bi_pure _ _) => mDesAndPureR Hn
      | @bi_and _ (@bi_pure _ _) _ => mDesAndPureL Hn
      | @iNW ?Hn' ?x =>
        match Hn' with
        | Hn => idtac
        | _ => let Hn' := get_fresh_name_tac Hn' in mRename Hn into Hn'
        end; on_current ltac:(fun H => unfold iNW in H at 1)
      | _ => mDes' tl
      end
    end.

  Ltac mDes :=
    match goal with
    | _: @current_iPropL _ _ ?l |- _ => mDes' l
    end.

  Ltac mDesAll :=
    repeat mDes.

  Section TEST.

    Variable ctx: Σ.
    Hypothesis WF: URA.wf ctx.

    Notation "Hns 'TO' Hns'" := ((current_iPropL ctx Hns) -> (current_iPropL ctx Hns')) (at level 60).
    Ltac check := erewrite f_equal; [eassumption|refl].

    (* check tactic *)
    Goal ∀ X, [("A", X)] TO [("B", X)].
    Proof. i. mDesAll. Fail check. Abort.

    (* iNW *)
    Goal ∀ X, [("A", << "A"; X >>)] TO [("A", X)].
    Proof. i. mDesAll. check. Qed.

    Goal ∀ P Q X Y, [("A", <<"A"; X>>); ("H", <<"B"; P>> ** <<"C"; Q>>); ("B", <<"D"; Y>>)] TO
                     [("D", Y); ("B1", P); ("C", Q); ("A", X)].
    Proof. i. mDesAll. check. Qed.

  End TEST.




















  Let wf: W -> Prop :=
    @mk_wf _ unit
           (fun _ _stk_mgr0 _ =>
              ⌜True⌝ ** (∃ (stk_mgr0: gmap mblock (list Z)),
                            (⌜_stk_mgr0 = stk_mgr0↑⌝) ∧
                            (<<"SIM"; ([∗ map] handle ↦ stk ∈ stk_mgr0,
                                       (∃ hd, OwnM ((handle, 0%Z) |-> [hd]) ** is_list hd (map Vint stk)))>>)
                        ))
           (* (fun _ _ _ => ⌜True⌝%I) *)
           top4
  .

  Variable global_stb: list (string * fspec).
  Hypothesis STBINCL: stb_incl (DebugStb ++ StackStb ++ MemStb) global_stb.

  Ltac renamer :=
    match goal with
    | [mp_src: gmap nat (list Z) |- _ ] =>
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
    econstructor 1 with (wf:=wf); ss; et; swap 2 3.
    { econs; ss. eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iClear "H". iSplits; ss. }
    econs; ss.
    { unfold newF. trivial_init. fold wf. mDesAll; des; subst. ss.
      unfold new_body, KModSem.transl_fun_tgt, ccall, cfun. steps.

      kstart 1.
      kcatch. { eapply STBINCL. stb_tac; ss. } hcall _ (Some _) _ with "SIM"; ss; et.
      { iModIntro. rewrite Any.pair_split. iSplits; ss; et. instantiate (1:=1%nat). ss. }
      { ss. }
      Ltac post_call :=
        fold wf; clear_fast; mDesAll; des_safe; subst; try rewrite Any.upcast_downcast in *; clarify; renamer.
      post_call. rename a0 into handle.
      steps. kstop. steps.

      force_l. exists handle. steps. rewrite Any.upcast_downcast. steps.
      destruct (stk_mgr0 !! handle) eqn:T.
      { mAssertPure False; ss.
        (*** IEXPLOIT*) iDestruct (big_sepM_lookup_acc with "SIM") as "[B C]"; et. iDestruct "B" as (x) "[B D]".
        iApply (points_to_disj with "A B"); et.
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
      { iModIntro. rewrite Any.pair_split. iFrame; ss; et. }
      { ss. }
      post_call. unhide_k. steps. rewrite Any.upcast_downcast in *. clarify.
      hide_k.

      destruct stk as [|x stk1]; ss.
      - mDesAll. subst.
        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "SIM POST"; ss.
        { iModIntro. rewrite Any.pair_split. iSplitL "SIM"; ss; [et|]. iSplits; ss. repeat iRight. et. }
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
        { iModIntro. rewrite Any.pair_split. iSplitL "SIM"; ss. { et. } iSplits; ss; et. }
        post_call. unhide_k. steps. rewrite Any.upcast_downcast in *. clarify. steps.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "SIM POST1"; ss.
        { iModIntro. rewrite Any.pair_split. iSplitL "SIM"; ss; et. }
        post_call. steps.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "SIM A2"; ss.
        { iModIntro. rewrite Any.pair_split. iSplitL "SIM"; ss; et. }
        post_call. steps.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "SIM POST2"; ss.
        { iModIntro. rewrite Any.pair_split. iSplitL "SIM"; ss; et. }
        post_call. steps.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "SIM POST1"; ss.
        { iModIntro. rewrite Any.pair_split. iSplitL "SIM"; ss; et. }
        post_call. steps.

        kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "SIM POST"; ss.
        { iModIntro. rewrite Any.pair_split. iSplitL "SIM"; ss; et. }
        post_call. steps.

        kstop. steps. rewrite Any.upcast_downcast. steps. renamer.
        destruct (alist_find "debug" (DebugStb ++ StackStb ++ MemStb)) eqn:U; cycle 1.
        { exfalso. stb_tac. ss. }
        dup U. revert U. stb_tac. clarify. i.
        apply STBINCL in U. rewrite U. steps.

        destruct (stk_mgr1 !! handle) eqn:V.
        { mAssertPure False; ss. iDestruct (big_sepM_lookup_acc with "SIM") as "[B C]"; et.
          iDestruct "B" as (y) "[SIM B]".
          iApply (points_to_disj with "POST1 SIM"). }

        hcall _ _ _ with "SIM POST1 A"; ss; et.
        { iModIntro. iSplits; ss; et. iApply big_sepM_insert; ss. iFrame. iExists _; ss. iFrame. }
        { ss. }
        steps.

        hret _; ss. iModIntro. iSplitL; ss.
    }
    econs; ss.
    { unfold pushF. trivial_init. fold wf. mDesAll; des; subst. ss.
      unfold push_body, KModSem.transl_fun_tgt, ccall, cfun. steps.

      rewrite Any.upcast_downcast in *; clarify. steps. kstart 7.

      hide_k. destruct v, v0; ss. des_ifs. clear_tac.
      rename n into handle. renamer. rename l into stk. rename _UNWRAPU into T.
      mAssert _ with "SIM".
      { iDestruct (big_sepM_delete with "SIM") as "[B C]"; et. (* big_sepM_lookup_acc *)
        instantiate (1:=_ ** _). iSplitL "B". { iExact "B". } iExact "C". }
      mDesAll; ss. renamer. rename a into hd.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some _) _ with "SIM"; ss; et.
      { iModIntro. rewrite Any.pair_split. iSplitL "SIM"; et. iSplits; ss; et. instantiate (1:=2). ss. }
      post_call. rename a0 into node. unhide_k. steps. rewrite Any.upcast_downcast in *. clarify. steps.

      rewrite points_to_split in ACC. mDesOwn "A1". rewrite Z.add_0_l in *. clear_fast.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "A SIM"; ss; et.
      { iModIntro. rewrite Any.pair_split. iSplitL "SIM"; et. }
      post_call. steps.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "A1 SIM"; ss; et.
      { iModIntro. rewrite Any.pair_split. iSplitL "SIM"; et. }
      post_call. steps.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "A3 SIM"; ss; et.
      { iModIntro. rewrite Any.pair_split. iSplitL "SIM"; et. }
      post_call. steps.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "POST SIM"; ss; et.
      { iModIntro. rewrite Any.pair_split. iSplitL "SIM"; et. }
      post_call. steps.

      kstop. steps. rewrite Any.upcast_downcast. steps.

      destruct (alist_find "debug" (DebugStb ++ StackStb ++ MemStb)) eqn:U; cycle 1.
      { exfalso. stb_tac. ss. }
      dup U. revert U. stb_tac. clarify. i.
      apply STBINCL in U. rewrite U. steps.

      destruct (stk_mgr1 !! handle) eqn:V.
      { mAssertPure False; ss. iDestruct (big_sepM_lookup_acc with "SIM") as "[B C]"; et.
        iDestruct "B" as (y) "[SIM B]". iApply (points_to_disj with "POST3 SIM"). }

      hcall _ _ _ with "-"; ss; et.
      { iModIntro. iSplits; ss; et.
        iApply big_sepM_insert; ss. iFrame. iExists _; ss. iFrame.
        iExists _, _. iFrame. iSplit; ss. erewrite points_to_split with (hd:=Vint z) (tl:=[hd]).
        iSplitL "POST1"; et.
      }
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
    econs; ss. ii. eapply sim_modsem; ss.
  Qed.

End SIMMOD.
