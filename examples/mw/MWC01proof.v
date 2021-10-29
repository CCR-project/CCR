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

  Let W: Type := Any.t * Any.t.

  Variant sim_opt (opt: Z -> option val) (vs: list val): Prop :=
  | sim_opt_intro
      (* (SIM: ∀ k, 0 <= k < 100 -> opt k = List.nth_error vs (Z.to_nat k)) *)
      (SIM: ∀ k v, 0 <= k < 100 -> opt k = Some v -> List.nth_error vs (Z.to_nat k) = Some v)
  .

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (* (fun _ _ mpr_tgt => (∃ (mr_tgt: AppRA), ⌜mpr_tgt = Any.pair tt↑ (GRA.embed mr_tgt)↑⌝ ** OwnM mr_tgt)%I) *)
      (fun _ mp_src mp_tgt =>
         (* (∃ lst0, ⌜mp_src = lst0↑⌝ ** (∃ blk vs, ⌜mp_tgt = (Vptr blk 0, lst0.(lst_map))↑⌝ ** OwnM ((blk,0%Z) |-> vs)) ∨ *)
         (*                               (⌜mp_tgt = (Vnullptr, lst0.(lst_map))↑⌝))%I) *)


         (* (∃ lst0 blk vs, ⌜mp_src = lst0↑⌝ ** ⌜mp_tgt = (Vptr blk 0, lst0.(lst_map))↑⌝ ** OwnM ((blk,0%Z) |-> vs) ** *)
         (*     ⌜sim_opt lst0.(lst_opt) vs ∧ (if dec lst0.(lst_map) Vnullptr then (lst0.(lst_opt) = Maps.empty) else length vs = 100)⌝)%I) *)
         (* (∃ lst0 blk vs, ⌜mp_src = lst0↑⌝ ** ⌜mp_tgt = (Vptr blk 0, lst0.(lst_map))↑⌝ ** *)
         (*                                      (OwnM ((blk,0%Z) |-> vs) ** ⌜sim_opt lst0.(lst_opt) vs⌝ ** ⌜length vs = 100⌝) ∨ *)
         (*                                      (⌜lst0.(lst_map) = Vnullptr⌝))%I) *)
         (∃ lst0 arr, ⌜mp_src = lst0↑⌝ ** ⌜mp_tgt = (arr, lst0.(lst_map))↑⌝ ** ({{"CASES":
            (⌜arr = Vnullptr ∧ lst0.(lst_map) = Vnullptr ∧ lst0.(lst_opt) = Maps.empty⌝) ∨
            (∃ arrb vs, ⌜arr = Vptr arrb 0 ∧ lst0.(lst_map) = Vnullptr ∧ lst0.(lst_opt) = Maps.empty ∧ length vs = 100⌝ ** OwnM ((arrb,0%Z) |-> vs)) ∨
            (∃ arrb vs, ⌜arr = Vptr arrb 0 ∧ lst0.(lst_map) <> Vnullptr ∧ length vs = 100⌝ ** OwnM ((arrb,0%Z) |-> vs))
         }}))%I)
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
    i. econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { ss. }
    { esplits; et. econs; et. eapply to_semantic. iIntros "H". iSplits; ss; et. }
    (* { destruct (SkEnv.id2blk (Sk.load_skenv sk) "arr") eqn:T; cycle 1. *)
    (*   { exfalso. Local Transparent Sk.load_skenv. unfold Sk.load_skenv in *. Local Opaque Sk.load_skenv. *)
    (*     ss. uo. des_ifs. admit "ez". } *)
    (*   esplits. econs; ss. eapply to_semantic. iIntros "H". rewrite T. cbn. iSplits; ss; et. *)
    (*   { rewrite points_to_nil. iApply OwnM_unit; ss. } *)
    (* } *)

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u. steps. unfold mainF, MWC0.mainF. steps. rename a into lst0.
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
