Require Import HoareDef MWHeader MWAppImp MWApp9 SimModSem.
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

  Definition to_val (b: bool): val := if b then Vint 1 else Vint 0.

  Let wf (ske: SkEnv.t): _ -> W -> Prop :=
    @mk_wf _ (option (Any.t * Any.t))
           (fun w0 st_src st_tgt => (
                {{"NORMAL": ∃ initv, ⌜w0 = None ∧ st_src = initv↑⌝ **
                    OwnM (var_points_to ske "initialized" (to_val initv))}} ∨
                {{"LOCKED": ⌜(∃ p0, st_src = Any.pair tt↑ p0) ∧ w0 = Some (st_src, st_tgt)⌝%I}})%I
           )
  .

  Variable global_stb: Sk.t -> gname -> option fspec.
  (* Hypothesis INCLMW: stb_incl (to_stb (MWStb)) global_stb. *)
  (* Hypothesis INCLMEM: stb_incl (to_stb (MemStb)) global_stb. *)
  Hypothesis STBINCL: forall sk, stb_incl (to_stb_context ["put"; "get"] (MemStb))
                                          (global_stb sk).

  Import ImpNotations.

  Ltac isteps := repeat (steps; imp_steps).

  Theorem correct:
    refines2 [MWAppImp.App] [MWApp9.App (global_stb)].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf (Sk.load_skenv sk)) (le:=le); et; ss; swap 2 3.
    { typeclasses eauto. }
    { eexists. econs. eapply to_semantic. iIntros "A". iLeft. iSplits; ss; et. }

    eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF.
    hexploit (SKINCL "initialized"); ss; eauto. intros [blk0 FIND0].

    econs; ss.
    { kinit. harg. mDesAll; des; clarify. unfold initF, MWAppImp.initF, ccallU.
      set (Sk.load_skenv sk) as ske in *.
      fold (wf ske).
      isteps. rewrite unfold_eval_imp. isteps.
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { rewrite Any.pair_split. steps. }
      rewrite Any.upcast_split. steps.
      match goal with [|- context[ ListDec.NoDup_dec ?a ?b ]] => destruct (ListDec.NoDup_dec a b) end; cycle 1.
      { contradict n. solve_NoDup. }
      isteps.
      astart 1. astep "load" (tt↑). { eapply STBINCL. stb_tac; ss. } rewrite FIND0. isteps.
      hcall _ (Some (_, _, _)) _ with "A".
      { iModIntro. iSplitR; iSplits; ss; et. unfold var_points_to. rewrite FIND0. iFrame. }
      { esplits; ss; et. }
      fold (wf ske). ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. rewrite Any.upcast_downcast. steps. isteps. astop. steps.
      assert(T: wf_val (to_val a)).
      { destruct a; ss. }
      apply Any.pair_inj in H2. des; clarify. clear_fast. steps.
      assert(U: is_true (to_val a) = Some a).
      { destruct a; ss. }
      rewrite U. steps.
      des_ifs.
      - steps. isteps.
        Local Transparent syscalls.
        cbn. steps. isteps.
        hret None; ss.
        { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. unfold var_points_to. des_ifs. }
      - steps. isteps.
        erewrite STBINCL; [|stb_tac; ss]. steps.
        hcall _ None _ with "*".
        { iModIntro. iSplits; ss; et.
          - iLeft. iSplits; ss; et. unfold var_points_to. rewrite FIND0. rewrite FIND1. iFrame.
            iSplits; ss; et.
          - iPureIntro. ii. apply Any.upcast_inj in H0. des; clarify. admit "size argument". }
        { esplits; ss; et. }
        fold (wf ske). mDesAll; des; clarify.
        mDesOr "INV"; mDesAll; des; clarify; ss. steps. isteps.
        Local Transparent syscalls.
        cbn. des_ifs. steps. isteps. hret None; ss.
        { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }


        Local Transparent syscalls.
        cbn. steps. isteps.
        hret None; ss.
        { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. unfold var_points_to. des_ifs. }
      -
      assert(Y: wf_val v).
      des_ifs.
    }

    econs; ss.
    { eapply _loop_sim; et. }

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
          - rewrite scale_int_8 in *. uo. clarify. ss. rewrite Z.add_0_l.
            unfold modrange_64. unfold scale_ofs. bsimpl; des.
            destruct (Z_le_gt_dec 0 (8 * z)); cycle 1.
            { lia. }
            destruct (Z_lt_ge_dec (8 * z) modulus_64); ss.
            unfold modulus_64, wordsize_64 in *.
            rewrite two_power_nat_equiv in *. lia.
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
        cbn. des_ifs. steps. isteps. hret None; ss.
        { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
      - isteps. replace (intrange_64 (- 1)) with true by ss. unfold unint in *. des_ifs_safe.
        steps.
        bsimpl; des; des_sumbool.
        + destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z).
          { lia. }
          isteps.
          destruct ((ZArith_dec.Z_lt_dec z 100)%Z); cycle 1.
          { lia. }
          isteps.
          rewrite FIND1. steps. isteps.
          astart 1. astep "load" (tt↑). { eapply STBINCL. stb_tac; ss. }
          hcall _ (Some (_, _, _)) _ with "A".
          { iModIntro. iSplitR; iSplits; ss; et. unfold var_points_to. rewrite FIND1. iFrame. }
          { esplits; ss; et. }
          fold (wf ske). ss. des_ifs. clear_fast.
          mDesOr "INV"; mDesAll; des; clarify; ss. rewrite Any.upcast_downcast. steps. astop. isteps.
          erewrite STBINCL; [|stb_tac; ss]. steps.
          apply Any.pair_inj in H2. des; clarify.
          hcall _ _ None with "*".
          { iModIntro. iSplits; ss; et.
            iLeft. iSplits; ss; et. iFrame. unfold var_points_to. rewrite FIND1. iFrame. iSplits; ss; et.
          }
          { esplits; ss; et. }
          fold (wf ske). mDesAll; des; clarify.
          mDesOr "INV"; mDesAll; des; clarify; ss. steps. isteps.
          hret None; ss.
          { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
        + destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z); cycle 1.
          { lia. }
          isteps.
          destruct ((ZArith_dec.Z_lt_dec z 100)%Z).
          { lia. }
          isteps.
          rewrite FIND1. steps. isteps.
          astart 1. astep "load" (tt↑). { eapply STBINCL. stb_tac; ss. }
          hcall _ (Some (_, _, _)) _ with "A".
          { iModIntro. iSplitR; iSplits; ss; et. unfold var_points_to. rewrite FIND1. iFrame. }
          { esplits; ss; et. }
          fold (wf ske). ss. des_ifs. clear_fast.
          mDesOr "INV"; mDesAll; des; clarify; ss. rewrite Any.upcast_downcast. steps. astop. isteps.
          erewrite STBINCL; [|stb_tac; ss]. steps.
          apply Any.pair_inj in H2. des; clarify.
          hcall _ _ None with "*".
          { iModIntro. iSplits; ss; et.
            iLeft. iSplits; ss; et. iFrame. unfold var_points_to. rewrite FIND1. iFrame. iSplits; ss; et.
          }
          { esplits; ss; et. }
          fold (wf ske). mDesAll; des; clarify.
          mDesOr "INV"; mDesAll; des; clarify; ss. steps. isteps.
          hret None; ss.
          { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
    }

    econs; ss.
    { kinit. harg. mDesAll; des; clarify. unfold getF, MWCImp.getF, ccallU.
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
        { clear - PURE1 _UNWRAPU0 Heq. r in PURE1. des_ifs; ss; clarify.
          - unfold wf_val. rewrite Z.add_0_l. unfold intrange_64. bsimpl; des; des_sumbool.
            destruct (Z_le_gt_dec min_64 (8 * z)); ss; cycle 1.
            { unfold min_64, modulus_64_half, modulus_64, wordsize_64 in *.
              rewrite two_power_nat_S in *. rewrite Z.mul_comm in *. rewrite Z.div_mul in *; ss.
              rewrite two_power_nat_equiv in *. lia. }
            destruct (Z_le_gt_dec (8 * z) max_64); ss; cycle 1.
            { unfold max_64, modulus_64_half, modulus_64, wordsize_64 in *.
              apply Z.leb_le in Heq. apply Z.ltb_lt in Heq0.
              rewrite two_power_nat_S in *. set (8 * z)%Z as y in *. rewrite Z.mul_comm in *.
              rewrite Z.div_mul in *; ss. rewrite two_power_nat_equiv in *. lia. }
          - rewrite scale_int_8 in *. uo. clarify. ss. rewrite Z.add_0_l.
            unfold modrange_64. unfold scale_ofs. bsimpl; des.
            destruct (Z_le_gt_dec 0 (8 * z)); cycle 1.
            { lia. }
            destruct (Z_lt_ge_dec (8 * z) modulus_64); ss.
            unfold modulus_64, wordsize_64 in *.
            rewrite two_power_nat_equiv in *. lia.
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
        cbn. des_ifs. steps. isteps. hret None; ss.
        { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
      - isteps. replace (intrange_64 (- 1)) with true by ss. unfold unint in *. des_ifs_safe.
        steps.
        bsimpl; des; des_sumbool.
        + destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z).
          { lia. }
          isteps.
          destruct ((ZArith_dec.Z_lt_dec z 100)%Z); cycle 1.
          { lia. }
          isteps.
          rewrite FIND1. steps. isteps.
          astart 1. astep "load" (tt↑). { eapply STBINCL. stb_tac; ss. }
          hcall _ (Some (_, _, _)) _ with "A".
          { iModIntro. iSplitR; iSplits; ss; et. unfold var_points_to. rewrite FIND1. iFrame. }
          { esplits; ss; et. }
          fold (wf ske). ss. des_ifs. clear_fast.
          mDesOr "INV"; mDesAll; des; clarify; ss. rewrite Any.upcast_downcast. steps. astop. isteps.
          erewrite STBINCL; [|stb_tac; ss]. steps.
          apply Any.pair_inj in H2. des; clarify.
          hcall _ _ None with "*".
          { iModIntro. iSplits; ss; et.
            iLeft. iSplits; ss; et. iFrame. unfold var_points_to. rewrite FIND1. iFrame. iSplits; ss; et.
          }
          { esplits; ss; et. }
          fold (wf ske). mDesAll; des; clarify.
          mDesOr "INV"; mDesAll; des; clarify; ss. steps. isteps.
          hret None; ss.
          { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
        + destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z); cycle 1.
          { lia. }
          isteps.
          destruct ((ZArith_dec.Z_lt_dec z 100)%Z).
          { lia. }
          isteps.
          rewrite FIND1. steps. isteps.
          astart 1. astep "load" (tt↑). { eapply STBINCL. stb_tac; ss. }
          hcall _ (Some (_, _, _)) _ with "A".
          { iModIntro. iSplitR; iSplits; ss; et. unfold var_points_to. rewrite FIND1. iFrame. }
          { esplits; ss; et. }
          fold (wf ske). ss. des_ifs. clear_fast.
          mDesOr "INV"; mDesAll; des; clarify; ss. rewrite Any.upcast_downcast. steps. astop. isteps.
          erewrite STBINCL; [|stb_tac; ss]. steps.
          apply Any.pair_inj in H2. des; clarify.
          hcall _ _ None with "*".
          { iModIntro. iSplits; ss; et.
            iLeft. iSplits; ss; et. iFrame. unfold var_points_to. rewrite FIND1. iFrame. iSplits; ss; et.
          }
          { esplits; ss; et. }
          fold (wf ske). mDesAll; des; clarify.
          mDesOr "INV"; mDesAll; des; clarify; ss. steps. isteps.
          hret None; ss.
          { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
    }
  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
