Require Import HoareDef MWHeader MWC8 MWC9 SimModSem.
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

  Definition wf (ske: SkEnv.t): _ -> W -> Prop :=
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
  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk,
      stb_incl (to_stb_context ["Map.new"; "Map.access"; "Map.update"; "App.init"; "App.run"; "MW.loop"]
                               (MemStb)) (global_stb sk).

  Theorem correct:
    refines2 [MWC8.MW] [MWC9.MW (global_stb)].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf (Sk.load_skenv sk)) (le:=le); et; ss; swap 2 3.
    { typeclasses eauto. }
    { eexists. econs. eapply to_semantic. iIntros "[A B]". iLeft. iSplits; ss; et. iFrame. iSplits; ss; et. }

    eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF.
    hexploit (SKINCL "gv0"); ss; eauto 10. intros [blk0 FIND0].
    hexploit (SKINCL "gv1"); ss; eauto 10. intros [blk1 FIND1].

    econs; ss.
    { init. harg. mDesAll; des; clarify. unfold mainF, MWC8.mainF, ccallU.
      set (Sk.load_skenv sk) as ske in *.
      fold (wf ske).
      steps.
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { rewrite Any.pair_split. steps. }
      rewrite Any.upcast_split. steps.
      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps. rewrite FIND0. steps. rewrite FIND1. steps.
      hcall None None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. iPureIntro. esplits; ss; et. }
      { esplits; ss; et. }
      fold (wf ske). mDesAll; des; clarify. steps.
      mDesOr "INV"; mDesAll; des; clarify; ss.
      unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *.
      astart 1. astep "store" (tt↑). { eapply STBINCL. stb_tac; ss. } hcall (Some (_, _, _)) _ with "A1".
      { iModIntro. iSplitR; iSplits; ss; et. }
      { esplits; ss; et. }
      fold (wf ske). unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. steps. astop. steps.

      apply Any.pair_inj in H2. des; clarify.
      unfold unblk in *. des_ifs.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. unfold var_points_to. rewrite FIND0. rewrite FIND1. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. steps.

      astart 1. astep "store" (tt↑). { eapply STBINCL. stb_tac; ss. } steps.
      hcall (Some (_, _, _)) _ with "A".
      { iModIntro. iSplitR; iSplits; ss; et. }
      { esplits; ss; et. }
      fold (wf ske). unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. steps. astop. steps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. unfold var_points_to in *. rewrite FIND0. rewrite FIND1. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. steps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. unfold var_points_to in *. rewrite FIND0. rewrite FIND1. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. steps.

      hret None; ss.
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. unfold var_points_to in *. rewrite FIND0. rewrite FIND1. iFrame. ss. }
    }

    econs; ss.
    { init. harg. mDesAll; des; clarify. unfold loopF, MWC8.loopF, ccallU.
      set (Sk.load_skenv sk) as ske in *.
      fold (wf ske).
      steps.
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { rewrite Any.pair_split. steps. }
      rewrite Any.upcast_split. steps.
      steps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. steps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. steps.

      hret None; ss.
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
    }

    econs; ss.
    { init. harg. mDesAll; des; clarify. unfold putF, MWC8.putF, ccallU.
      set (Sk.load_skenv sk) as ske in *.
      fold (wf ske).
      steps.
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { rewrite Any.pair_split. steps. }
      rewrite Any.upcast_split. steps.
      des_ifs.
      - steps. ss. clarify. rewrite FIND0. rewrite FIND1. steps. force_r. esplits; ss. steps.

        astart 1. astep "load" (tt↑). { eapply STBINCL. stb_tac; ss. } steps.
        hcall (Some (_, _, _)) _ with "A1".
        { iModIntro. iSplitR; iSplits; ss; et. unfold var_points_to. rewrite FIND0. iFrame. }
        { esplits; ss; et. }
        fold (wf ske). ss. des_ifs.
        mDesOr "INV"; mDesAll; des; clarify; ss. rewrite Any.upcast_downcast. steps. astop. steps.
        apply Any.pair_inj in H2. des; clarify. clear_fast.
        assert(Y: wf_val v1).
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
        rewrite Y. steps. erewrite STBINCL; [|stb_tac; ss]. steps. force_r; ss. steps.
        hcall None _ with "*".
        { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et.
          unfold var_points_to. rewrite FIND0. rewrite FIND1. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold (wf ske). mDesAll; des; clarify.
        mDesOr "INV"; mDesAll; des; clarify; ss. steps.
        hret None; ss.
        { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
      - unfold unint in *. des_ifs_safe.
        steps. rewrite FIND0. rewrite FIND1. steps. force_r. esplits; ss. steps.

        astart 1. astep "load" (tt↑). { eapply STBINCL. stb_tac; ss. }
        hcall (Some (_, _, _)) _ with "A".
        { iModIntro. iSplitR; iSplits; ss; et. unfold var_points_to. rewrite FIND1. iFrame. }
        { esplits; ss; et. }
        fold (wf ske). ss. des_ifs. clear_fast.
        mDesOr "INV"; mDesAll; des; clarify; ss. rewrite Any.upcast_downcast. steps. astop. steps.
        erewrite STBINCL; [|stb_tac; ss]. steps.
        apply Any.pair_inj in H2. des; clarify.
        hcall _ None with "*".
        { iModIntro. iSplits; ss; et.
          iLeft. iSplits; ss; et. iFrame. unfold var_points_to. rewrite FIND1. iFrame. iSplits; ss; et.
        }
        { esplits; ss; et. }
        fold (wf ske). mDesAll; des; clarify.
        mDesOr "INV"; mDesAll; des; clarify; ss. steps.
        hret None; ss.
        { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
    }

    econs; ss.
    { init. harg. mDesAll; des; clarify. unfold getF, MWC8.getF, ccallU.
      set (Sk.load_skenv sk) as ske in *.
      fold (wf ske).
      steps.
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { rewrite Any.pair_split. steps. }
      rewrite Any.upcast_split. rewrite FIND0. rewrite FIND1. steps.
      des_ifs.
      - steps.
        destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z); cycle 1.
        { lia. }
        steps.
        destruct ((ZArith_dec.Z_lt_dec z 100)%Z); cycle 1.
        { lia. }
        steps. force_r; esplits; ss. steps.

        astart 1. astep "load" (tt↑). { eapply STBINCL. stb_tac; ss. } steps.
        hcall (Some (_, _, _)) _ with "A1".
        { iModIntro. iSplitR; iSplits; ss; et. unfold var_points_to. rewrite FIND0. iFrame. }
        { esplits; ss; et. }
        fold (wf ske). ss. des_ifs.
        mDesOr "INV"; mDesAll; des; clarify; ss. rewrite Any.upcast_downcast. steps. astop. steps.
        apply Any.pair_inj in H2. des; clarify. clear_fast.
        assert(Y: wf_val v0).
        { clear - PURE1 _UNWRAPU1 Heq. r in PURE1. des_ifs; ss; clarify.
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
        rewrite Y. steps. steps. erewrite STBINCL; [|stb_tac; ss]. steps. force_r; ss. steps.
        hcall None _ with "*".
        { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. unfold var_points_to.
          rewrite FIND0. rewrite FIND1. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold (wf ske). mDesAll; des; clarify.
        mDesOr "INV"; mDesAll; des; clarify; ss. steps.
        Local Transparent syscalls.
        cbn. des_ifs. steps. hret None; ss.
        { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
      - steps. unfold unint in *. des_ifs_safe. force_r; esplits; ss.
        steps.
        astart 1. astep "load" (tt↑). { eapply STBINCL. stb_tac; ss. }
        hcall (Some (_, _, _)) _ with "A".
        { iModIntro. iSplitR; iSplits; ss; et. unfold var_points_to. rewrite FIND1. iFrame. }
        { esplits; ss; et. }
        fold (wf ske). ss. des_ifs. clear_fast.
        mDesOr "INV"; mDesAll; des; clarify; ss. rewrite Any.upcast_downcast. steps. astop. steps.
        erewrite STBINCL; [|stb_tac; ss]. steps.
        apply Any.pair_inj in H2. des; clarify.
        hcall _ None with "*".
        { iModIntro. iSplits; ss; et.
          iLeft. iSplits; ss; et. iFrame. unfold var_points_to. rewrite FIND1. iFrame. iSplits; ss; et.
        }
        { esplits; ss; et. }
        fold (wf ske). mDesAll; des; clarify.
        mDesOr "INV"; mDesAll; des; clarify; ss. steps.
        hret None; ss.
        { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
    }

  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
