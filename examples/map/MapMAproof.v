Require Import HoareDef MapHeader MapM MapA SimModSem.
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

Require Import HTactics2 HSim2 ISim2 ProofMode IProofMode2 STB Invariant.
Require Import Mem1 MemOpen.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.
  Context `{Σ: GRA.t}.

  Context `{@GRA.inG MapRA0 Σ}.
  Context `{@GRA.inG MapRA1 Σ}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := Any.t * Any.t.

  Definition initial_map_r: @URA.car MapRA1 :=
    (Excl.unit, Auth.excl ((fun _ => Excl.just 0%Z): @URA.car (Z ==> (Excl.t Z))%ra) ((fun _ => Excl.just 0%Z): @URA.car (Z ==> (Excl.t Z))%ra)).

  Definition black_map_r (f: Z -> Z): @URA.car MapRA1 :=
    (Excl.unit, Auth.black ((fun k => Excl.just (f k)): @URA.car (Z ==> (Excl.t Z))%ra)).

  Definition unallocated_r (sz: Z): @URA.car MapRA1 :=
    (Excl.unit, Auth.white ((fun k =>
                               if (Z_gt_le_dec 0 k) then Excl.just 0%Z
                               else if (Z_gt_le_dec sz k) then Excl.unit else Excl.just 0%Z)
                             : @URA.car (Z ==> (Excl.t Z))%ra)).

  Definition initial_map: iProp :=
    OwnM initial_map_r.

  Definition black_map (f: Z -> Z): iProp :=
    OwnM (black_map_r f).

  Definition unallocated (sz: Z): iProp :=
    OwnM (unallocated_r sz).

  Lemma unallocated_alloc (sz: nat)
    :
    unallocated sz -∗ (map_points_to sz 0 ** unallocated (Z.pos (Pos.of_succ_nat sz))).
  Proof.
    unfold map_points_to, unallocated. iIntros "H".
    replace (unallocated_r sz) with ((map_points_to_r sz 0) ⋅ (unallocated_r (S sz))).
    { ss. iDestruct "H" as "[H0 H1]". iFrame. }
    unfold unallocated_r, map_points_to_r. ur. f_equal.
    { ur. auto. }
    { ur. unfold Auth.white. f_equal. ur. extensionality k.
      ur. des_ifs; try by (exfalso; lia).
    }
  Qed.

  Lemma initial_map_initialize sz
    :
    initial_map -∗ (black_map (fun _ => 0%Z) ** initial_points_tos sz ** unallocated sz).
  Proof.
    induction sz.
    { ss. iIntros "H". unfold initial_map.
      replace initial_map_r with ((black_map_r (fun _ => 0%Z)) ⋅ (unallocated_r 0)).
      { iDestruct "H" as "[H0 H1]". iFrame. }
      { unfold initial_map_r, black_map_r, unallocated_r. ur. f_equal.
        { ur. auto. }
        { ur. f_equal. ur. extensionality k. ur. des_ifs. }
      }
    }
    { iIntros "H". iPoseProof (IHsz with "H") as "H". ss.
      iDes. iPoseProof (unallocated_alloc with "A") as "A". iFrame. auto.
    }
  Qed.

  Lemma initial_map_no_points_to k v
    :
    initial_map -∗ map_points_to k v -∗ ⌜False⌝.
  Proof.
    unfold initial_map, map_points_to.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". exfalso. rr in H2. ur in H2. unseal "ra". des.
    rr in H3. ur in H3. unseal "ra". des.
    rr in H3. des. ur in H3. eapply equal_f with (x:=k) in H3.
    ur in H3. des_ifs.
  Qed.

  Lemma unallocated_range sz k v
    :
    unallocated sz -∗ map_points_to k v -∗ ⌜(0 <= k < sz)%Z⌝.
  Proof.
    unfold unallocated, map_points_to.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". iPureIntro. rr in H2. ur in H2. unseal "ra". des.
    rr in H3. ur in H3. unseal "ra".
    rr in H3. ur in H3. unseal "ra". specialize (H3 k).
    rr in H3. ur in H3. unseal "ra". des_ifs. lia.
  Qed.

  Lemma black_map_get f k v
    :
    black_map f -∗ map_points_to k v -∗ (⌜f k = v⌝).
  Proof.
    unfold black_map, map_points_to.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". iPureIntro. rr in H2. ur in H2. unseal "ra". des.
    rr in H3. ur in H3. unseal "ra". des.
    rr in H3. des. ur in H3. eapply equal_f with (x:=k) in H3.
    ur in H3. des_ifs.
  Qed.

  Lemma black_map_set f k w v
    :
    black_map f -∗ map_points_to k w -∗ #=> (black_map (fun n => if Z.eq_dec n k then v else f n) ** map_points_to k v).
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iPoseProof (OwnM_Upd with "H") as "H".
    { instantiate (1:=black_map_r (fun n => if Z.eq_dec n k then v else f n) ⋅ map_points_to_r k v).
      rr. i. ur in H2. ur. unseal "ra". des_ifs. des. split; auto.
      ur in H3. ur. des_ifs. des. rr in H3. des. split.
      { rr. exists ctx. ur in H3. ur. extensionality n.
        eapply equal_f with (x:=n) in H3. ur in H3. ur. des_ifs.
      }
      { ur. i. rr. ur. unseal "ra". ss. }
    }
    iMod "H". iDestruct "H" as "[H0 H1]". iFrame. auto.
  Qed.

  Let wf: _ -> W -> Prop :=
        @mk_wf
          _ unit
          (fun _ st_src st_tgt =>
             ((∃ f sz, ⌜st_src = f↑ /\ st_tgt = (f, sz)↑⌝ ** black_map f ** unallocated sz ** pending1) ∨ (initial_map ** ⌜st_src = (fun (_: Z) => 0%Z)↑ /\ st_tgt = (fun (_: Z) => 0%Z, 0%Z)↑⌝))%I).

  Let GlobalStb: (Sk.t → string → option fspec) := fun _ => to_stb (MemStb ++ MapStb).
  Let GlobalStbM: (Sk.t → string → option fspec) := fun _ => to_stb (MemStb ++ MapStbM).
  Hint Unfold GlobalStb: stb. 
  Hint Unfold GlobalStbM: stb.

  (* Variable GlobalStbM: Sk.t -> gname -> option fspec. *)
  (* Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM. *)

  (* Variable GlobalStb: Sk.t -> gname -> option fspec. *)
  (* Hypothesis STB_set: forall sk, (GlobalStb sk) "set" = Some set_spec. *)

  (* Hypothesis PUREINCL: forall sk, stb_pure_incl (GlobalStbM sk) (GlobalStb sk). *)

  Lemma pending1_unique:
    pending1 -∗ pending1 -∗ False%I.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". exfalso. clear - H2.
    rr in H2. ur in H2. unseal "ra". des.
    rr in H2. ur in H2. unseal "ra". ss.
  Qed.

  Theorem correct: refines2 [MapM.Map GlobalStbM] [MapA.Map GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits. rp; [econs|..]; try refl; cycle 1. { rewrite URA.unit_idl. refl. }
         eapply to_semantic. iIntros "H". iRight; eauto. }
    Local Opaque initial_map black_map map_points_to unallocated.
    econs; [|ss].
    { econs; r; ss. startproof.
      cbn. unfold MapM.initF, MapA.initF, cfunN, cfunU, ccallN, ccallU. cbn.
      i. esplits; ss. i.
      iIntros. iDes. subst. unfold pending. iDes. iFrame. unfold inv_with. iDes.
      { iExFalso. iApply (pending1_unique with "A0 A3"). }
      des; subst. iModIntro. iSplits; ss. steps.
      iDestruct (initial_map_initialize with "A") as "A". iDes.
      steps. iApply isim_apc_both. iSplitR "A1".
      { unfold inv_with. iSplits; ss. iLeft. iSplits; ss. iFrame. iSplits; et. }
      iIntros. iDes. steps. iIntros. iDes. iModIntro. iFrame.
    }
    econs; [|ss].
    { econs; r; ss. startproof.
      unfold MapM.getF, MapA.getF, ccallU, ccallN. cbn. i. esplits; ss. { des_ifs. } steps.
      iIntros. iDes. unfold inv_with. iDes.
      2:{ iExFalso; ss. iApply (initial_map_no_points_to with "A A1"). }
      des; subst. iFrame. iModIntro. iSplits; ss; et.
      steps.
      iAssert (⌜(0 ≤ x_src0 < sz)%Z⌝)%I as "%".
      { iApply (unallocated_range with "[A3]"); eauto. }
      force_r; ss. steps.
      iAssert (⌜_⌝)%I as "%".
      { iApply (black_map_get with "A A1"). }
      subst.
      iApply isim_apc_both. iSplitR "A1".
      { unfold inv_with. iSplits; ss. iLeft. iSplits; ss. iFrame. iSplits; ss. }
      iIntros. iDes. clear_fast. steps. iIntros. iDes.
      iModIntro. iFrame. iSplits; ss.
    }
    econs; [|ss].
    { econs; r; ss. startproof.
      unfold MapM.setF, MapA.setF, ccallU, ccallN. cbn. i. esplits; ss. { des_ifs. } steps.
      iIntros. iDes. unfold inv_with. iDes.
      2:{ iExFalso; ss. iApply (initial_map_no_points_to with "A A1"). }
      des; subst. iFrame. iModIntro. iSplits; ss; et.
      steps.
      iAssert (⌜(0 ≤ x_src2 < sz)%Z⌝)%I as "%".
      { iApply (unallocated_range with "[A3]"); eauto. }
      force_r; ss. steps.
      iAssert (_)%I with "[A A1]" as "A".
      { iApply (black_map_set with "A A1"). }
      iMod "A". iDes.
      iApply isim_apc_both. iSplitR "A0".
      { unfold inv_with. iSplits; ss. iLeft. iSplits; ss. iFrame. iSplits; ss. }
      iIntros. iDes. clear_fast. steps. iIntros. iDes.
      iModIntro. iFrame. iSplits; ss.
    }
    econs; [|ss].
    { econs; r; ss. startproof.
      unfold MapM.set_by_userF, MapA.set_by_userF, ccallU, ccallN. cbn. i. esplits; ss. { des_ifs. } steps.
      iIntros. iDes. subst. unfold inv_with. iDes.
      2:{ iExFalso; ss. iApply (initial_map_no_points_to with "A A1"). }
      des; subst. iFrame. iModIntro. iSplits; ss; et.
      steps.
      iApply isim_syscall. iIntros. steps. iSplits; ss; et.
      iIntros. iExists (_, _, _). iSplits; ss; et. iIntros. iDes. iSplitR "".
      { unfold inv_with. iFrame. iSplits; ss; et. iLeft. iFrame. iSplits; ss; et. iFrame. iSplits; ss; et. }
      iIntros. iDes. subst. iFrame. iSplits; ss; et. steps. iIntros. iDes. iModIntro.
      unfold inv_with. iDes.
      2:{ des; subst. iPoseProof (initial_map_no_points_to with "A1 A0") as "H"; ss. }
      des; subst. iFrame. iSplitR "A0".
      { iSplits; ss; et. iLeft. iFrame. iSplits; ss; et. iFrame. iSplits; ss; et. }
      { iSplits; ss; et. }
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
