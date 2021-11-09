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
      (SIM: ∀ k (IN: (0 <= k < 100)%Z),
          <<INIT: lst0.(lst_cls) k = opt ∧ vs !! (Z.to_nat k) = Some (lst0.(lst_opt) k)>> ∨
          <<UNINIT: lst0.(lst_cls) k = uninit ∧ vs !! (Z.to_nat k) = Some Vundef>>)
      (NORMAL: ∀ k (NOTIN: ~(0 <= k < 100)%Z), lst0.(lst_cls) k = normal \/ lst0.(lst_cls) k = uninit)
      (LEN: length vs = 100)
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

  (* Let X := (gset nat). *)
  (* Let x: X. r. *)
  (* Check (elements a). *)
  (* Set Printing All. *)
  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      (option (Any.t * Any.t))
      (fun w0 mp_src mp_tgt =>
         ({{"UNINIT": OwnM sp_black ** ⌜mp_src = tt↑ ∧ w0 = None ∧ ∃ (arr map: val), mp_tgt = (arr, map)↑⌝}} ∨
          {{"INIT": OwnM sp_black **
             ∃ lst0 arr vs, ⌜mp_src = lst0↑ ∧ mp_tgt = (Vptr arr 0%Z, lst0.(lst_map))↑ ∧ w0 = None ∧
                            sim_opt lst0 vs⌝ ** ([∗ list] k ↦ x ∈ vs, OwnM ((arr, Z.of_nat k) |-> [x]))}} ∨
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

  Lemma repeat_replicate
        A (a: A) n
    :
      repeat a n = replicate n a
  .
  Proof.
    induction n; ii; ss. rewrite IHn. f_equal; ss.
  Qed.

  Opaque List.repeat.

  (* Lemma repeat_nil *)
  (*       V (v: V) *)
  (*   : *)
  (*     repeat v 0 = nil *)
  (* . *)
  (* Proof. ss. Qed. *)

  (* Lemma repeat_snoc *)
  (*       V n (v: V) *)
  (*   : *)
  (*     repeat v (S n) = (repeat v n) ++ [v] *)
  (* . *)
  (* Proof. replace (S n) with (n + 1) by lia. rewrite repeat_app. ss. Qed. *)
  Opaque replicate.

  Lemma replicate_nil
        V (v: V)
    :
      replicate 0 v = nil
  .
  Proof. ss. Qed.

  Lemma points_to_app
        blk ofs hd tl
    :
      (points_to (blk, ofs) (hd ++ tl)) =
      (points_to (blk, ofs) hd) ⋅ (points_to (blk, (ofs + length hd)%Z) tl)
  .
  Proof.
    revert ofs tl. induction hd; ii; ss.
    - rewrite points_to_nil. rewrite URA.unit_idl. rewrite Z.add_0_r. ss.
    - rewrite points_to_split. rewrite IHhd.
      erewrite points_to_split with (hd:=a) (tl:=hd). rewrite URA.add_assoc. do 3 f_equal. lia.
  Qed.

  (* Lemma points_to_snoc *)
  (*       blk ofs x tl *)
  (*   : *)
  (*     (points_to (blk, ofs) (tl ++ [x])) = *)
  (*     (points_to (blk, ofs) tl) ⋅ (points_to (blk, (ofs + length tl)%Z) [x]) *)
  (* . *)
  (* Proof. rewrite points_to_app. ss. Qed. *)

  (* Lemma points_to_app *)
  (*       blk ofs hd tl *)
  (*   : *)
  (*     (points_to (blk, ofs) (hd ++ tl)) = (points_to (blk, ofs) hd) ⋅ (points_to (blk, (ofs + length hd)%Z) tl) *)
  (* . *)
  (* Proof. *)
  (*   revert ofs hd. induction tl; ii; ss. *)
  (*   - rewrite points_to_nil. rewrite app_nil_r. rewrite URA.unit_id. ss. *)
  (*   - rewrite cons_app. rewrite IHtl. rewrite app_assoc. rewrite IHtl. ss. rewrite points_to_split. *)
  (*     rewrite points_to_snoc. rewrite <- ! URA.add_assoc. f_equal. f_equal. rewrite points_to_nil. *)
  (*     rewrite URA.unit_idl. rewrite app_length. ss. rewrite <- Z.add_assoc. rewrite ! Nat2Z.inj_add. ss. *)
  (* Qed. *)

  Lemma OwnM_replicate_sepL
        v n b
    :
        bi_entails (OwnM ((b, 0%Z) |-> replicate n v))
                   (#=> [∗ list] k↦x ∈ replicate n v, OwnM ((b, Z.of_nat k) |-> [x]))
  .
  Proof.
    induction n.
    { iIntros "H". rewrite replicate_nil. ss. rewrite points_to_nil. iClear "H". iModIntro. ss. }
    { rewrite ! replicate_S_end. iIntros "H".
      iApply big_sepL_snoc.
      rewrite points_to_split. rewrite points_to_app. iDestruct "H" as "[A B]". rewrite Z.add_0_l.
      iDestruct (IHn with "A") as "C". iFrame. rewrite points_to_nil. rewrite URA.unit_id.
      iMod "C". iModIntro. iFrame.
    }
  Qed.

  Lemma sim_init: forall v,
      sim_opt {| lst_cls := λ _, uninit; lst_opt := λ _, Vundef; lst_map := v |} (replicate 100 Vundef).
  Proof.
    econs; ii; ss; et.
    - right. esplits; et. rewrite lookup_replicate_2; ss. lia.
  Qed.

  Lemma sim_upd
        k v lst0 vs0 (SIM: sim_opt lst0 vs0) (OPT: lst_cls lst0 k = opt) (IN: (0 <= k < 100)%Z)
    :
      sim_opt {| lst_cls := lst_cls lst0; lst_opt := set k v (lst_opt lst0); lst_map := lst_map lst0 |}
              (<[Z.to_nat k:=v]> vs0).
  Proof.
    i. inv SIM. econs; et; cycle 1.
    { rewrite insert_length; ss. }
    i. destruct (dec k k0); subst; ss.
    - exploit SIM0; et. intro T; des.
      + left. esplits; et. unfold set. des_ifs. rewrite list_lookup_insert; ss. eapply lookup_lt_is_Some_1; et.
      + rewrite OPT in *; ss.
    - exploit SIM0; et. i; des.
      + left. esplits; et. unfold set. des_ifs. rewrite list_lookup_insert_ne; ss. ii.
        apply Z2Nat.inj in H1; ss.
      + right. esplits; et. rewrite list_lookup_insert_ne; ss. ii.
        apply Z2Nat.inj in H1; ss.
  Qed.

  Lemma sim_upd2
        k v lst0 vs0 (SIM: sim_opt lst0 vs0) (OPT: lst_cls lst0 k = uninit) (IN: (0 <= k < 100)%Z)
    :
      sim_opt {| lst_cls := set k opt (lst_cls lst0);
                 lst_opt := set k v (lst_opt lst0); lst_map := lst_map lst0 |}
              (<[Z.to_nat k:=v]> vs0).
  Proof.
    i. inv SIM. econs; ss; et; cycle 1.
    { ii. unfold set. des_ifs. exploit NORMAL; et. }
    { rewrite insert_length; ss. }
    i. unfold set. des_ifs.
    - left. esplits; et. rewrite list_lookup_insert; ss. lia.
    - exploit SIM0; et. i; des.
      + left. esplits; ss; et. rewrite list_lookup_insert_ne; ss. ii. apply Z2Nat.inj in H1; ss.
      + right. esplits; ss; et. rewrite list_lookup_insert_ne; ss. ii. apply Z2Nat.inj in H1; ss.
  Qed.

  Lemma sim_upd3
        k lst0 vs0 (SIM: sim_opt lst0 vs0) (OPT: lst_cls lst0 k = uninit) (IN: ~(0 <= k < 100)%Z)
    :
      sim_opt {| lst_cls := set k normal (lst_cls lst0);
                 lst_opt := (lst_opt lst0); lst_map := lst_map lst0 |} vs0.
  Proof.
    i. inv SIM. econs; ss; et; cycle 1.
    { ii. unfold set. des_ifs; ss; et. }
    i. unfold set. des_ifs; et.
  Qed.


  Theorem correct: refines2 [MWC0.MW] [MWC1.MW].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=le); et; swap 2 3.
    { typeclasses eauto. }
    { esplits; et. econs; et. eapply to_semantic. iIntros "H". ss; et. iFrame. iLeft. iSplits; ss; et. }
    (* { destruct (SkEnv.id2blk (Sk.load_skenv sk) "arr") eqn:T; cycle 1. *)
    (*   { exfalso. Local Transparent Sk.load_skenv. unfold Sk.load_skenv in *. Local Opaque Sk.load_skenv. *)
    (*     ss. uo. des_ifs. admit "ez". } *)
    (*   esplits. econs; ss. eapply to_semantic. iIntros "H". rewrite T. cbn. iSplits; ss; et. *)
    (*   { rewrite points_to_nil. iApply OwnM_unit; ss. } *)
    (* } *)

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u. steps. unfold mainF, MWC0.mainF, ccallU. steps. fold wf.
      mAssert (OwnM sp_black ** OwnM sp_white ** ⌜w = None ∧ ∃ (arr map: val), mp_tgt = (arr, map)↑⌝) with "*" as "A".
      { iDes; des; clarify; try (by iFrame; iSplits; ss; et). admit "ez". }
      mDesAll; des; clarify.
      astart 1. acatch. hcall _ 100 (Some (_, _)) with "*".
      { iModIntro. iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. steps. astop. mDesAll; des; clarify.
      mDesOr "INV"; mDesAll; des; clarify; ss.
      mDesOr "INV"; mDesAll; des; clarify; ss.
      steps. force_l; stb_tac; ss; clarify. steps.
      hcall _ _ _ with "-A".
      { iModIntro. iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify.
      mDesOr "INV"; mDesAll; des; clarify; ss.
      mDesOr "INV"; mDesAll; des; clarify; ss. steps.
      hcall _ _ _ with "*".
      { rewrite repeat_replicate. iDestruct (OwnM_replicate_sepL with "A") as "A". iMod "A".
        iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et.
        - iPureIntro. eapply sim_init.
      }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.

      hcall _ _ _ with "*".
      { iModIntro. iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. ss. des_ifs.
      hret None; ss.
      { iModIntro. iFrame. iSplits; ss; et. }
    }

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u.
      assert(w = None).
      { repeat mDesOr "INV"; mDesAll; des; clarify. mAssertPure False; ss. admit "ez". }
      steps. unfold loopF, MWC0.loopF, ccallU. steps. fold wf.
      force_l; stb_tac; ss; clarify. steps. hcall _ _ _ with "*".
      { iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps. hcall _ _ _ with "*".
      { iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. ss. des_ifs.
      hret None; ss.
      { iModIntro. iFrame; et. }
    }

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u. unfold putF, MWC0.putF, ccallU. steps. fold wf.
      force_r; ss. esplits; ss. steps.
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
      - inv PURE2. hexploit (SIM (Z.to_nat z)); [lia|]. rewrite ! Nat2Z.id in *;rewrite Z2Nat.id in *;try lia.
        intro U. des; ss.
        + rewrite INIT. ss. steps.
          mAssert _ with "A2".
          { iDestruct (big_sepL_insert_acc with "A2") as "[B C]"; et.
            instantiate (1:=_ ** _). iSplitL "B". { iExact "B". } iExact "C". }
          mDesAll; ss. rewrite Z2Nat.id in *; try lia. rewrite scale_int_8. steps.
          astart 1. acatch. hcall _ (_, _, _) (Some (_, _)) with "-A2".
          { iModIntro. iFrame. iSplitR "A1"; et. }
          { esplits; ss; et. }
          fold wf. mDesAll; des; clarify. ss. des_ifs.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          steps. astop. steps. hret None; ss.
          { iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et; cycle 1.
            { iApply "A2"; et. }
            iPureIntro. eapply sim_upd; et; try lia. econs; et.
          }
        + rewrite UNINIT. ss. steps. force_l. exists true. steps. unfold set; ss. des_ifs. steps.
          mAssert _ with "A2".
          { iDestruct (big_sepL_insert_acc with "A2") as "[B C]"; et.
            instantiate (1:=_ ** _). iSplitL "B". { iExact "B". } iExact "C". }
          mDesAll; ss. rewrite Z2Nat.id in *; try lia. rewrite scale_int_8. steps.
          astart 1. acatch. hcall _ (_, _, _) (Some (_, _)) with "-A2".
          { iModIntro. iFrame. iSplitR "A1"; et. }
          { esplits; ss; et. }
          fold wf. mDesAll; des; clarify. ss. des_ifs.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          steps. astop. steps. hret None; ss.
          { iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et; cycle 1.
            { iApply "A2"; et. }
            iPureIntro. eapply sim_upd2; et; try lia. econs; et.
          }
      - steps.
        destruct (lst_cls l z) eqn:U.
        + ss. steps. force_l. exists false. steps. unfold set. des_ifs. steps. force_l; stb_tac; ss; clarify.
          steps. hcall _ _ _ with "A INIT".
          { iModIntro. iSplits; ss; et. iRight. iRight. iFrame. iSplits; ss; et. }
          { esplits; ss; et. }
          fold wf. ss. des_ifs.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          steps. hret None; ss.
          { iSplits; ss; et. iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et.
            iPureIntro. eapply sim_upd3; et; try lia. }
        + exfalso. inv PURE2. hexploit (NORMAL z); et. { lia. } intro V. rewrite U in *; des; ss.
        + ss. steps. rewrite U. ss. steps. force_l; stb_tac; ss; clarify. steps.
          hcall _ _ _ with "-A2".
          { iModIntro. iSplits; ss; et. iRight. iRight. iFrame. iSplits; ss; et. }
          { esplits; ss; et. }
          fold wf. ss. des_ifs.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          steps. hret None; ss.
          { iSplits; ss; et. iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et. }
    }

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u. unfold getF, MWC0.getF, ccallU. steps. fold wf.
      force_r. esplits; ss. steps.
      mDesOr "INV"; mDesAll; des; clarify.
      { exfalso. clear - _UNWRAPU1. apply Any.downcast_upcast in _UNWRAPU1. des.
        apply Any.upcast_inj in _UNWRAPU1. des; clarify.
        assert(T: exists (a b: local_state), a <> b).
        { exists (mk_lst (fun _ => uninit) (fun _ => Vundef) Vundef),
          (mk_lst (fun _ => uninit) (fun _ => Vundef) (Vint 1)). ii. clarify. }
        des. revert a b T. rewrite EQ. i. repeat des_u; ss.
      }
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { mAssertPure False; ss. admit "ez". }
      steps. rewrite Any.upcast_downcast in *. clarify. steps.
      destruct ((0 <=? z)%Z && (z <? 100)%Z) eqn:T.
      - inv PURE2. hexploit (SIM (Z.to_nat z)); [lia|]. rewrite ! Nat2Z.id in *;rewrite Z2Nat.id in *;try lia.
        intro U. des; ss.
        + rewrite INIT. ss. steps.
          mAssert _ with "A2".
          { iDestruct (big_sepL_delete with "A2") as "[B C]"; et. xtra. }
          mDesAll; ss. rewrite Z2Nat.id in *; try lia. rewrite scale_int_8. steps.
          astart 1. acatch. hcall _ (_, _, _) (Some (_, _)) with "-A2".
          { iModIntro. iFrame. iSplits; ss; et. }
          { esplits; ss; et. }
          fold wf. mDesAll; des; clarify. ss. des_ifs.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          steps. astop. steps. hret None; ss.
          { iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et; cycle 1.
            { iApply big_sepL_delete; et. rewrite Z2Nat.id. iFrame. lia. }
          }
      - steps. inv PURE2. exploit (NORMAL z); et. { lia. } intro U; des; clarify. rewrite U. ss.
        steps. force_l; stb_tac; ss; clarify. steps.
        hcall _ _ (Some (_, _)) with "-A2".
        { iModIntro. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. ss. des_ifs.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        steps. hret None; ss.
        { iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et. }
    }

  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
