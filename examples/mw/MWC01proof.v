Require Import HoareDef MWHeader MWC0 MWC1 SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import Mem1.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import HTactics IPM ProofMode STB.

Set Implicit Arguments.

Local Open Scope nat_scope.





Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG spRA Σ}.

  Let W: Type := Any.t * Any.t.

  Variant sim_opt (lst0: local_state) (vs: list val): Prop :=
  | sim_opt_intro
      (* (SIM: ∀ k (IN: 0 <= k < 100) (CLS: lst0.(lst_cls) k = opt), *)
      (*     <<SIM: List.nth_error vs (Z.to_nat k) = Some (lst0.(lst_opt) k)>>) *)
      (SIM: ∀ k (IN: 0 <= k < 100),
          <<INIT: lst0.(lst_cls) k = opt ∧ List.nth_error vs (Z.to_nat k) = Some (lst0.(lst_opt) k)>> ∨
          <<UNINIT: lst0.(lst_cls) k = uninit ∧ List.nth_error vs (Z.to_nat k) = Some Vundef>>)
  .

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

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      (option (Any.t * Any.t))
      (fun w0 mp_src mp_tgt =>
         ({{"UNINIT": OwnM sp_black ** ⌜mp_src = tt↑ ∧ w0 = None⌝}} ∨
          {{"INIT": OwnM sp_black ** ∃ lst0 arr vs, ⌜mp_src = lst0↑ ∧ mp_tgt = (arr, lst0.(lst_map))↑ ∧
                                                  sim_opt lst0 vs ∧ w0 = None⌝ ** OwnM ((arr, 0%Z) |-> vs)}} ∨
          {{"LOCKED": OwnM sp_black ** OwnM sp_white ** ⌜w0 = Some (mp_src, mp_tgt)⌝}})%I)
  .

  Lemma points_to_nil
        loc
    :
      <<EQ: loc |-> [] = ε>>
  .
  Proof.
    unfold points_to. r. rewrite unfold_points_to. des_ifs. ss.
    Local Transparent URA.unit. unfold URA.unit. ss. Local Opaque URA.unit.
    unfold Auth.white. f_equal. apply func_ext; i. apply func_ext; i. des_ifs.
    bsimpl; des; des_sumbool. clarify. lia.
  Qed.

  Opaque memRA.
  Opaque mwRA.
  Opaque Z.eq_dec Z.eqb.
  Opaque List.repeat.

  Theorem correct: refines2 [MWC0.MW] [MWC1.MW].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=le); et; swap 2 3.
    { typeclasses eauto. }
    { esplits; et. econs; et. eapply to_semantic. iIntros "H". ss; et. iFrame. ss; et. }
    (* { destruct (SkEnv.id2blk (Sk.load_skenv sk) "arr") eqn:T; cycle 1. *)
    (*   { exfalso. Local Transparent Sk.load_skenv. unfold Sk.load_skenv in *. Local Opaque Sk.load_skenv. *)
    (*     ss. uo. des_ifs. admit "ez". } *)
    (*   esplits. econs; ss. eapply to_semantic. iIntros "H". rewrite T. cbn. iSplits; ss; et. *)
    (*   { rewrite points_to_nil. iApply OwnM_unit; ss. } *)
    (* } *)

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u. steps. unfold mainF, MWC0.mainF, ccallU. steps. fold wf.
      mAssert (OwnM sp_black ** OwnM sp_white ** ⌜w = None⌝) with "*" as "A".
      { iDes; des; clarify; try (by iFrame; iSplits; ss; et). admit "ez". }
      mDesAll; des; clarify.
      astart 1. acatch. hcall _ 100 (Some (_, _)) with "*".
      { iModIntro. iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. steps. astop. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.
      hcall _ _ _ with "INV".
      { iModIntro. iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.
      mDesOr "INV1"; mDesAll; des; clarify; ss.
      mDesOr "INV1"; mDesAll; des; clarify; ss.
      hcall _ _ _ with "LOCKED A1".
      { iModIntro. iSplits; ss; et. iRight. iRight. iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.
      mDesOr "INV"; mDesAll; des; clarify; ss.
      mDesOr "INV"; mDesAll; des; clarify; ss.
      hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et. iFrame. iSplitL; ss; et. iRight. iLeft. iSplits; ss; et.
        iPureIntro. econs. ii. right. esplits; et. admit "ez".
      }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss.
      { hret None; ss. iModIntro. iFrame. ss; et. }
      mDesOr "INV"; mDesAll; des; clarify; ss.
      { hret None ;ss. iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et. }
    }

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u.
      assert(w = None).
      { repeat mDesOr "INV"; mDesAll; des; clarify. mAssertPure False; ss. admit "ez". }
      steps. unfold loopF, MWC0.loopF, ccallU. steps. fold wf.
      force_l; stb_tac; ss; clarify. steps. hcall _ _ _ with "INV".
      { iModIntro. ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps. hcall _ _ _ with "*".
      { iModIntro. iFrame. et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. ss. des_ifs.
      hret None; ss.
      { iModIntro. iFrame; et. }
    }

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u. unfold putF, MWC0.putF, ccallU. steps. fold wf.
      mDesOr "INV"; mDesAll; des; clarify.
      { exfalso. clear - _UNWRAPU0. apply Any.downcast_upcast in _UNWRAPU0. des.
        apply Any.upcast_inj in _UNWRAPU0. des; clarify.
        assert(T: exists (a b: local_state), a <> b).
        { exists (mk_lst (fun _ => uninit) (fun _ => Vundef) Vundef),
          (mk_lst (fun _ => uninit) (fun _ => Vundef) (Vint 1)). ii. clarify. }
        des. revert a b T. rewrite EQ. i. repeat des_u; ss.
      }
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { mAssertPure False; ss. admit "ez". }
      steps. rewrite Any.upcast_downcast in *. clarify. steps.
      destruct ((0 <=? z)%Z && (z <? 100)%Z) eqn:T.
      - inv PURE1. hexploit (SIM (Z.to_nat z)); [lia|]. intro U. des; ss.
        + rewrite ! Nat2Z.id in *. rewrite Z2Nat.id in *; try lia. rewrite INIT. ss. steps.
          astart 1. acatch. hcall _ (_, _, _) (Some (_, _)) with "*".
          { iModIntro. iFrame. iSplitR "A2"; et. iSplits; ss; et.
            - iPureIntro. f_equal. f_equal; et. f_equal; et.
            - et. iSplits; ss; et.
          exfalso.
          Set Printing All.
          Z2Nat.id
          rewrite ! Nat2Z.id in INIT.
          Set Printing All. des_ifs; ss. rewrite INIT. des_ifs; ss.
        { lia. }
        ss.
        autorewrite with simpl_bool in T; des.
        rewrite Z.leb_le in *. rewrite Z.ltb_lt in *.
      des.
        rewrite Any.upcast_downcast in _UNWRAPU0. fold wf. steps. }
      assert(w = None).
      { repeat mDesOr "INV"; mDesAll; des; clarify. mAssertPure False; ss. admit "ez". }
      steps. unfold putF, MWC0.putF, ccallU. steps. fold wf.
      force_l; stb_tac; ss; clarify. steps. hcall _ _ _ with "INV".
      { iModIntro. ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps. hcall _ _ _ with "*".
      { iModIntro. iFrame. et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. ss. des_ifs.
      hret None; ss.
      { iModIntro. iFrame; et. }
    }
    {
    }
      rename w into ww.
      {
      hcall _ _ _ with "*".
      
      - 
      {
      steps.
    }
      }
      mDesOr "INV"; mDesAll; des; clarify.
      { (** uninit **)
        astart 1. acatch. hcall _ 100 (Some (_, _)) with "*".
        { iModIntro. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. steps. astop. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.
        hcall _ _ _ with "INV".
        { iModIntro. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.
        mDesOr "INV1"; mDesAll; des; clarify; ss.
        mDesOr "INV1"; mDesAll; des; clarify; ss.
        hcall _ _ _ with "LOCKED A1".
        { iModIntro. iSplits; ss; et. iRight. iRight. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        hcall _ _ _ with "*".
        { iModIntro. iSplits; ss; et. iFrame. iSplitL; ss; et. iRight. iLeft. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. steps. ss. des_ifs.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        { hret None; ss. iModIntro. iFrame. ss; et. }
        mDesOr "INV"; mDesAll; des; clarify; ss.
        { hret None ;ss. iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et. }
      }
      mDesOr "INV"; mDesAll; des; clarify.
      { (** init **)
        mClear "A2".
        astart 1. acatch. hcall _ 100 (Some (_, _)) with "*".
        { iModIntro. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. steps. astop. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.
        hcall _ _ _ with "INV".
        { iModIntro. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.
        mDesOr "INV1"; mDesAll; des; clarify; ss.
        mDesOr "INV1"; mDesAll; des; clarify; ss.
        hcall _ _ _ with "LOCKED A1".
        { iModIntro. iSplits; ss; et. iRight. iRight. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        hcall _ _ _ with "*".
        { iModIntro. iSplits; ss; et. iFrame. iSplitL; ss; et. iRight. iLeft. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. steps. ss. des_ifs.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        { hret None; ss. iModIntro. iFrame. ss; et. }
        mDesOr "INV"; mDesAll; des; clarify; ss.
        { hret None ;ss. iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et. }
      }
      {
      unfold ccallU. steps. astart 1. acatch. hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et.
        { iPureIntro. instantiate (1:=100). cbn. refl. }
        { ss. }
      }
      { esplits; ss; et. }
      steps. astop. mDesAll. des; clarify. steps. force_l; stb_tac; clarify; ss. steps. rename a3 into arrb.
      hcall _ _ _ with "-A".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. }
      steps. clear_fast. mDesAll; des; clarify. rename a1 into arr. rename a into lst1. steps. rewrite _UNWRAPU0. steps.
      force_l; stb_tac; ss; clarify. steps.
      (* mDesOr "CASES"; mDesAll; des; clarify. *)
      rename v into mapb.
      hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et. iRight. cbn. iRight. iSplits; ss; et. }
      { esplits; ss; et. }
      clear_fast. mDesAll; des; clarify. steps. rename a into lst1. rename a1 into arr.
      force_l; stb_tac; ss; clarify. steps.
      hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. }
      steps. mDesAll; clarify. rewrite _UNWRAPU2. steps. hret _; ss.
      { iModIntro. iSplits; ss; et. }
    }

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u. steps. unfold loopF, MWC0.loopF, ccallU. steps.
      force_l; stb_tac; ss. steps.
      hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. }
      steps. mDesAll; clarify. rewrite _UNWRAPU0. steps. force_l; stb_tac; ss. steps.
      hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. }
      steps. mDesAll; clarify. rewrite _UNWRAPU1. steps. hret _; ss.
      { iModIntro. iSplits; ss; et. }
    }

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u. steps. unfold putF, MWC0.putF, ccallU. steps.
      des_ifs.
      - force_l. exists true. steps. astart 1. acatch.
        mDesOr "CASES"; mDesAll; des; clarify.
        mDesOr "CASES"; mDesAll; des; clarify. rename a1 into arrb. rename a2 into vs. rename a into lst0.
        hcall _ (_, _, _) _ with "*".
        { iModIntro. iSplits; ss; et. iSplitR.
          - iSplits; ss; et. iRight. iRight. iSplits; ss; et.
        {
      -
      force_l; stb_tac; ss. steps.
      hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. }
      steps. mDesAll; clarify. rewrite _UNWRAPU0. steps. force_l; stb_tac; ss. steps.
      hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. }
      steps. mDesAll; clarify. rewrite _UNWRAPU1. steps. hret _; ss.
      { iModIntro. iSplits; ss; et. }
    }

    {
      {
      rename a into lst0.
      unfold ccallU. steps. astart 1. acatch. hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et.
        { iPureIntro. instantiate (1:=100). cbn. refl. }
        { ss. }
      }
      { esplits; ss; et. }
      steps. astop. mDesAll. des; clarify. steps. force_l; stb_tac; clarify; ss. steps. rename a3 into arrb.
      hcall _ _ _ with "-A".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. }
      steps. clear_fast. mDesAll; des; clarify. rename a1 into arr. rename a into lst1. steps. rewrite _UNWRAPU0. steps.
      force_l; stb_tac; ss; clarify. steps.
      (* mDesOr "CASES"; mDesAll; des; clarify. *)
      rename v into mapb.
      hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et. iRight. cbn. iRight. iSplits; ss; et. }
      { esplits; ss; et. }
      clear_fast. mDesAll; des; clarify. steps. rename a into lst1. rename a1 into arr.
      force_l; stb_tac; ss; clarify. steps.
      hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. }
      steps. mDesAll; clarify. rewrite _UNWRAPU2. steps. hret _; ss.
      { iModIntro. iSplits; ss; et. }
    }
    {
    }
      {
      { iModIntro. iSplits; ss; et. }
      { 
      }
      clears lst0; clear lst0. clears a4; clear a4.
      mDesAll. des; clarify. steps. force_l; stb_tac; clarify; ss. steps. rewrite _UNWRAPU0. steps.
      hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et.
        - cbn. iPureIntro; ss. econs. ii. rewrite clear - PURE1. inv PURE1. econs. ii. repeat spc SIM.
          iLeft. iFrame. rewrite repeat_length. iSplits; ss; et.
        iPureIntro. econs.
      }
      { 

      { stb_tac.
        autounfold with stb; autorewrite with stb; simpl.
        stb_tac. }
      steps. force_l. exists true. steps. force_l. eexists. steps. unfold ccallU. steps.
      force_l; stb_tac; ss; clarify. steps.
      hcall _ _ _ with "*".
      { iModIntro. iSplits; ss; et.
        { iPureIntro. instantiate (1:=100). cbn. refl. }
        { ss. }
      }
      { esplits; ss; et.
      mDesOr "A".
      -
      steps. unfold initF, ASSUME, GUARANTEE. steps.
      force_r. exists Init. steps. force_r; ss. steps. force_r. eexists. steps. force_r; ss.
      { esplits; et. admit "ez". }
      steps. rename c0 into rm. rename c1 into ro. rename c into rf1.
      rewrite URA.unit_id in _GUARANTEE0.
      mCombine "A1" "A2". mEval ltac:(erewrite URA.add_comm; erewrite <- _GUARANTEE0) in "A1".
      unfold ccallU. steps. des. clear_tac. mDesOwn "A1" as "B" "C".
      hcall _ (_, _, _) _ with "A B".
      { iModIntro. iDestruct "B" as "[B C]". iFrame. iSplits; ss; et. }
      { esplits; ss; et. rr; ss. }
      steps. mDesAll; clarify.
      rewrite _UNWRAPU. steps. force_r. exists ε. steps. force_r; ss. steps. force_r. rename a into rm0.
      eexists. steps. force_r; ss.
      { rewrite URA.unit_id. esplits; et. admit "ez". }
      steps. des; clarify.
      mAssert _ with "C A".
      { iCombine "A" "C" as "A". (* sym in _GUARANTEE. iRewrite _GUARANTEE in "A". *) iExact "A". }
      mEval ltac:(erewrite <- _GUARANTEE) in "A1".

      hret _; ss.
      { iModIntro. iDestruct "A1" as "[[A B] C]". iFrame. iSplitL "A"; et. }
    }

    econs; ss.
    { init. harg. mDesAll. des; clarify. rename x into mwf. rename a into _lower_layer_rm.
      steps. unfold runF, ASSUME, GUARANTEE. steps.
      force_r. exists Run. steps. force_r; ss. steps. force_r. eexists. steps. force_r; ss.
      { esplits; et. admit "ez". }
      steps. rename c0 into rm. rename c1 into ro. rename c into rf1.
      rewrite URA.unit_id in _GUARANTEE0.
      mCombine "A1" "A2". mEval ltac:(erewrite URA.add_comm; erewrite <- _GUARANTEE0) in "A1".
      unfold ccallU. steps. des. clear_tac. mDesOwn "A1" as "B" "C".
      hcall _ (_, _, _) _ with "A B".
      { iModIntro. iDestruct "B" as "[B C]". iFrame. iSplits; ss; et. }
      { esplits; ss; et. rr; ss. }
      steps. mDesAll; clarify.
      rewrite _UNWRAPU. steps. rewrite Any.upcast_downcast in *. clarify. steps.
      force_r. exists ε. steps. force_r; ss. steps. force_r. rename a into rm0.
      eexists. steps. force_r; ss.
      { rewrite URA.unit_id. esplits; et. admit "ez". }
      steps. des; clarify.
      mAssert _ with "C A".
      { iCombine "A" "C" as "A". (* sym in _GUARANTEE. iRewrite _GUARANTEE in "A". *) iExact "A". }
      mEval ltac:(erewrite <- _GUARANTEE) in "A2".

      hret _; ss.
      { iModIntro. iDestruct "A2" as "[[A B] C]". iFrame. iSplitL "A"; et. }
    }
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
