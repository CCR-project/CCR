Require Import HoareDef MWHeader MWCImp MWC9 SimModSem.
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

Require Import HTactics.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB.

Set Implicit Arguments.

Local Open Scope nat_scope.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition le (w0 w1: option (Any.t * Any.t)): Prop :=
    match w0, w1 with
    | Some w0, Some w1 => w0 = w1
    | None, None => True
    | _, _ => False
    end
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. unfold le. ii. des_ifs. Qed.
  Next Obligation. unfold le. ii. des_ifs. Qed.

  Let W: Type := Any.t * Any.t.

  (* Let wf: unit -> W -> Prop := *)
  (*   fun _ '(mrps_src0, mrps_tgt0) => *)
  (*     (<<SRC: mrps_src0 = tt↑>>) /\ *)
  (*     (<<TGT: mrps_tgt0 = tt↑>>) *)
  (* . *)
  Definition wf_arr (arr: val): Prop :=
    match arr with
    | Vint n => n = 0%Z
    | Vptr _ ofs => ofs = 0%Z
    | _ => False
    end
  .

  Let wf (ske: SkEnv.t): _ -> W -> Prop :=
    @mk_wf _ (option (Any.t * Any.t))
           (fun w0 st_src st_tgt => (
                {{"NORMAL": ∃ arr map, ⌜w0 = None ∧ st_src = (arr, map)↑ ∧ wf_arr arr⌝ **
                    OwnM (var_points_to ske "gv0" arr) ** OwnM (var_points_to ske "gv1" map)}} ∨
                (* {{"NORMAL": ∃ arr map arrb mapb, ⌜w0 = None ∧ ske.(SkEnv.id2blk) "gv0" = Some arrb *)
                (*     ∧ ske.(SkEnv.id2blk) "gv1" = Some mapb ∧ st_src = (arr, map)↑⌝ ** *)
                (*     OwnM ((arrb, 0%Z) |-> [arr]) ** OwnM ((mapb, 0%Z) |-> [map ])}} ∨ *)
                {{"LOCKED": ⌜(∃ p0, st_src = Any.pair tt↑ p0) ∧ w0 = Some (st_src, st_tgt)⌝%I}})%I
              (* ⌜True⌝ ** (∃ (stk_mgr0: gmap mblock (list val)), *)
              (*            (⌜_stk_mgr0 = stk_mgr0↑⌝) ∧ *)
              (*            ({{"SIM": ([∗ map] handle ↦ stk ∈ stk_mgr0, *)
              (*                       (∃ hd, OwnM ((handle, 0%Z) |-> [hd]) ** is_list hd stk))}}) *)
           )
  .

  Variable global_stb: gname -> option fspec.
  (* Hypothesis INCLMW: stb_incl (to_stb (MWStb)) global_stb. *)
  (* Hypothesis INCLMEM: stb_incl (to_stb (MemStb)) global_stb. *)
  Hypothesis STBINCL: stb_incl (to_stb_context ["new"; "access"; "update"; "init"; "run"]
                                               (MWStb ++ MemStb)) global_stb.

  Import ImpNotations.

  Theorem correct:
    refines2 [MWCImp.MW] [MWC9.MW (fun _ => global_stb)].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf (Sk.load_skenv sk)) (le:=le); et; ss; swap 2 3.
    { typeclasses eauto. }
    { eexists. econs. eapply to_semantic. iIntros "[A B]". iLeft. iSplits; ss; et. iFrame. iSplits; ss; et. }

    eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF.
    hexploit (SKINCL "gv0"); ss; eauto. intros [blk0 FIND0].
    hexploit (SKINCL "gv1"); ss; eauto 10. intros [blk1 FIND1].

    econs; ss.
    { kinit. harg. mDesAll; des; clarify. unfold mainF, MWCImp.mainF, ccallU.
      set (Sk.load_skenv sk) as ske in *.
      fold (wf ske).
      Ltac isteps := repeat (steps; imp_steps).
      isteps. rewrite unfold_eval_imp. isteps.
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { rewrite Any.pair_split. steps. }
      rewrite Any.upcast_split. steps.
      des_ifs; cycle 1.
      { contradict n. solve_NoDup. }
      steps. erewrite STBINCL; cycle 1. { stb_tac; ss. } isteps.
      hcall _ None None with "*".
      { iModIntro. iSplits; ss; et.
        - iLeft. iSplits; ss; et. iFrame. iPureIntro. esplits; ss; et.
        - admit "ez - size argument".
      }
      { esplits; ss; et. }
      fold (wf ske). mDesAll; des; clarify. steps. isteps. rewrite FIND0. steps.
      isteps. ss. des_ifs. mDesOr "INV"; mDesAll; des; clarify; ss.
      unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *.
      astart 1. astep "store" (tt↑). { eapply STBINCL. stb_tac; ss. } hcall _ (Some (_, _, _)) _ with "A1".
      { iModIntro. iSplitR; iSplits; ss; et. }
      { esplits; ss; et. }
      fold (wf ske). rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps. astop. steps.

      apply Any.pair_inj in H2. des; clarify.
      unfold unblk in *. des_ifs.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. rewrite FIND0. rewrite FIND1. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      astart 1. astep "store" (tt↑). { eapply STBINCL. stb_tac; ss. } rewrite FIND1. isteps.
      hcall _ (Some (_, _, _)) _ with "A".
      { iModIntro. iSplitR; iSplits; ss; et. }
      { esplits; ss; et. }
      fold (wf ske). rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps. astop. steps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. rewrite FIND0. rewrite FIND1. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. rewrite FIND0. rewrite FIND1. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      hret None; ss.
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. rewrite FIND0. rewrite FIND1. iFrame. ss. }
    }

    econs; ss.
    { kinit. harg. mDesAll; des; clarify. unfold loopF, MWCImp.loopF, ccallU.
      set (Sk.load_skenv sk) as ske in *.
      fold (wf ske).
      isteps. rewrite unfold_eval_imp. isteps.
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { rewrite Any.pair_split. steps. }
      rewrite Any.upcast_split. steps.
      des_ifs; cycle 1.
      { contradict n. solve_NoDup. }
      steps. isteps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      hret None; ss.
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
    }

    econs; ss.
    { kinit. harg. mDesAll; des; clarify. unfold putF, MWCImp.putF, ccallU.
      set (Sk.load_skenv sk) as ske in *.
      fold (wf ske).
      isteps. rewrite unfold_eval_imp. isteps.
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { rewrite Any.pair_split. steps. }
      rewrite Any.upcast_split. steps.
      match goal with [|- context[ ListDec.NoDup_dec ?a ?b ]] => destruct (ListDec.NoDup_dec a b) end; cycle 1.
      { contradict n. solve_NoDup. }
      des_ifs.
      - isteps. ss. clarify. replace (intrange_64 0) with true by ss. cbn. steps.
        destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z); cycle 1.
        { lia. }
        isteps.
        destruct ((ZArith_dec.Z_lt_dec z 100)%Z); cycle 1.
        { lia. }
        isteps.

        astart 1. astep "load" (tt↑). { eapply STBINCL. stb_tac; ss. } rewrite FIND0. isteps.
        hcall _ (Some (_, _, _)) _ with "A1".
        { iModIntro. iSplitR; iSplits; ss; et. unfold var_points_to. rewrite FIND0. iFrame. }
        { esplits; ss; et. }
        fold (wf ske). ss. des_ifs.
        mDesOr "INV"; mDesAll; des; clarify; ss. rewrite Any.upcast_downcast. steps. isteps. astop. steps.
        apply Any.pair_inj in H2. des; clarify. clear_fast.
        assert(Y: wf_val v).
        { clear - PURE1 _UNWRAPU0 Heq0. r in PURE1. des_ifs; ss; clarify.
          - unfold wf_val. rewrite Z.add_0_l. unfold intrange_64. bsimpl; des; des_sumbool.
            destruct (Z_le_gt_dec min_64 (8 * z)); ss; cycle 1.
            { unfold min_64, modulus_64_half, modulus_64, wordsize_64 in *.
              rewrite two_power_nat_S in *. rewrite Z.mul_comm in *. rewrite Z.div_mul in *; ss.
              rewrite two_power_nat_equiv in *. lia. }
            destruct (Z_le_gt_dec (8 * z) max_64); ss; cycle 1.
            { unfold max_64, modulus_64_half, modulus_64, wordsize_64 in *.
              apply Z.leb_le in Heq0. apply Z.ltb_lt in Heq1.
              rewrite two_power_nat_S in *. set (8 * z)%Z as y in *. rewrite Z.mul_comm in *.
              rewrite Z.div_mul in *; ss. rewrite two_power_nat_equiv in *. lia. }
          - admit "TODO".
        }
        rewrite Y. steps. isteps. erewrite STBINCL; [|stb_tac; ss]. steps.
        hcall _ None _ with "*".
        { iModIntro. iSplits; ss; et.
          - iLeft. iSplits; ss; et. unfold var_points_to. rewrite FIND0. rewrite FIND1. iFrame.
            iSplits; ss; et.
          - iPureIntro. ii. apply Any.upcast_inj in H0. des; clarify. admit "size argument". }
        { esplits; ss; et. }
        fold (wf ske). mDesAll; des; clarify.
        mDesOr "INV"; mDesAll; des; clarify; ss. steps. isteps.
        Local Transparent syscalls.
        cbn. des_ifs. steps. isteps.
        TTTTTTTTTTTTTTTTTTTTTTTTTTTTTT
        astop. steps.
        isteps.
        +
      -
    }
        { esplits; ss; et. }
        fold (wf ske). ss. des_ifs.
        mDesOr "INV"; mDesAll; des; clarify; ss. rewrite Any.upcast_downcast. steps. isteps. astop. steps.
        { erewrite STBINCL; stb_tac; ss. } rewrite FIND0. isteps.
        hcall _ (Some (_, _, _)) _ with "A1".
        idtac.
        TTTTTTTTTTTTTTTTTTTTTTT
        rename a into aa.
        exfalso. Set Printing All.
        erewrite Any.upcast_downcast in _UNWRAPU. apply Any.upcast_inj in H2.
        replace (vadd a (Vint (8 * z))) with 
        rewrite Any.upcast_downcast in _UNWRAPU0. apply Any.upcast_inj in H2.
        unfold vadd.
        unfold vadd. uo. des_ifs.
        cbn.
        TTTTTTTTTTTTTTttt
        astart 1. acatch.
        des_ifs.
        + isteps. rewrite FIND0. steps. isteps.
          admit "".
        + isteps.
          
        assert(T: intrange_64 0 && intrange_64 n1 = true). { ss. clarify. unfold unint in *. des_ifs_safe. unfold intrange_64. cbn. cbn. des_ifs; ss.
      -
      des_ifs; cycle 1.
      { contradict n0. solve_NoDup. }
      steps. isteps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      hret None; ss.
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
    }
      {


      erewrite STBINCL; cycle 1. { stb_tac; ss. } isteps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et.
        - iLeft. iSplits; ss; et. iFrame. iPureIntro. esplits; ss; et.
        - admit "ez - size argument".
      }
      { esplits; ss; et. }
      fold (wf ske). mDesAll; des; clarify. steps. isteps. rewrite FIND0. steps.
      isteps. ss. des_ifs. mDesOr "INV"; mDesAll; des; clarify; ss.
      unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *.
      astart 1. astep "store" (tt↑). { eapply STBINCL. stb_tac; ss. } hcall _ (Some (_, _, _)) _ with "A1".
      { iModIntro. iSplitR; iSplits; ss; et. }
      { esplits; ss; et. }
      fold (wf ske). rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps. astop. steps.

      apply Any.pair_inj in H2. des; clarify.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. rewrite FIND0. rewrite FIND1. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      astart 1. astep "store" (tt↑). { eapply STBINCL. stb_tac; ss. } rewrite FIND1. isteps.
      hcall _ (Some (_, _, _)) _ with "A".
      { iModIntro. iSplitR; iSplits; ss; et. }
      { esplits; ss; et. }
      fold (wf ske). rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps. astop. steps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. rewrite FIND0. rewrite FIND1. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. rewrite FIND0. rewrite FIND1. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      hret None; ss.
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. rewrite FIND0. rewrite FIND1. iFrame. ss. }
    }

      astart 1. astop. steps.
      
      apply Any.upcast_downcast in _UNWRAPU2. des ;clarify.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. rewrite FIND0. rewrite FIND1.
        iFrame. iSplits; ss; et. }
      (to_stb_context ClientStb (EchoStb ++ StackStb))
      force_l; stb_tac; ss; clarify.
          T.
          acatch.
      ired.
      rewrite interp_imp_AddrOf.
      rewrite <- INCLMEM. force_l; stb_tac; ss; clarify.

      des_ifs.
      contradict n.
      solve_NoDup.
      list_tac.
      try lia.
      des_ifs_safe ltac:(try lia). ss.
      steps. 
    }
    unfold fF.
    unfold IntroFImpA.fF.
    (* Local Opaque vadd. *)
    steps.
    rewrite unfold_eval_imp. cbn. steps.
    (* eapply Any.downcast_upcast in _UNWRAPN. des. *)
    unfold unint, ccallU in *. destruct v; clarify; ss.
    des_ifs; try (by exfalso; apply n; solve_NoDup).
    - repeat (steps; (des_ifs; try lia; []); imp_steps). r; esplits; et.
    - repeat (steps; (des_ifs; try lia; []); imp_steps). r; esplits; et.
    - repeat (steps; (des_ifs; try lia; []); imp_steps).
      unfold Ncall.
      steps. des_ifs.
      + repeat (steps; (des_ifs; try lia; []); imp_steps).
        force_l. exists false. steps. force_l. esplits. steps.
        force_l; ss. repeat (steps; (des_ifs; try lia; []); imp_steps).
        rewrite Z.eqb_eq in *. clarify.
        r; esplits; et.
      + repeat (steps; (des_ifs; try lia; []); imp_steps).
        force_l. exists true.
        unfold ccallU.
        repeat (steps; (des_ifs; try lia; []); imp_steps).
        force_l; ss.
        repeat (steps; (des_ifs; try lia; []); imp_steps).
        r; esplits; et. do 2 f_equal. lia.
  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
