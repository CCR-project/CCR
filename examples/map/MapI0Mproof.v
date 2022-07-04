Require Import MapHeader MapI0 MapM HoareDef SimModSem.
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
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB Invariant.

Set Implicit Arguments.

Local Open Scope nat_scope.




Section SIMMODSEM.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG MapRA0 Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
        @inv_wf
          _ _
          unit
          (fun _ st_src st_tgt =>
             ((∃ blk ofs l (f: Z -> Z) (sz: Z), ⌜st_src = (f, sz)↑ /\ (length l = Z.to_nat sz) /\ (forall k (SZ: (0 <= k < sz)%Z), nth_error l (Z.to_nat k) = Some (f k)) /\ st_tgt = (Vptr blk ofs)↑⌝ ** OwnM ((blk, ofs) |-> (List.map Vint l)) ** pending0) ∨ (⌜st_src = (fun (_: Z) => 0%Z, 0%Z)↑⌝))%I)
  .

  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Hypothesis STBINCLM: forall sk, stb_incl (to_stb MemStb) (GlobalStbM sk).
  Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM.

  Lemma pending0_unique:
    pending0 -∗ pending0 -∗ False%I.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". exfalso. clear - H1.
    rr in H1. ur in H1. unseal "ra". ss.
  Qed.

  Lemma points_to_get_split blk ofs l k v
        (GET: nth_error l k = Some v)
    :
    OwnM((blk, ofs) |-> l) -∗ (OwnM((blk, (ofs + k)%Z) |-> [v])) ** ((OwnM((blk, (ofs + k)%Z) |-> [v]) -* OwnM((blk, ofs) |-> l))).
  Proof.
    revert blk ofs k v GET. induction l; ss; i.
    { destruct k; ss. }
    destruct k; ss.
    { clarify. iIntros "H". rewrite points_to_split.
      iDestruct "H" as "[H0 H1]". iSplitL "H0".
      { rewrite Z.add_0_r. ss. }
      iIntros "H". iSplitL "H".
      { rewrite Z.add_0_r. ss. }
      { ss. }
    }
    { iIntros "H". rewrite points_to_split.
      iDestruct "H" as "[H0 H1]".
      iPoseProof (IHl with "H1") as "H1"; eauto.
      iDestruct "H1" as "[H1 H2]".
      replace (ofs + Z.pos (Pos.of_succ_nat k))%Z with (ofs + 1 + k)%Z by lia.
      iSplitL "H1"; auto. iIntros "H1". iSplitL "H0"; auto.
      iApply "H2". auto.
    }
  Qed.

  Lemma set_nth_success A (l: list A) (k: nat) v
        (SZ: k < length l)
    :
    exists l', set_nth k l v = Some l'.
  Proof.
    revert k v SZ. induction l; ss; i.
    { exfalso. lia. }
    { destruct k; ss; eauto.
      hexploit IHl; eauto.
      { instantiate (1:=k). lia. }
      i. des. rewrite H1. eauto.
    }
  Qed.

  Lemma points_to_set_split blk ofs l k v l'
        (GET: set_nth k l v = Some l')
    :
    OwnM((blk, ofs) |-> l) -∗ (∃ v', OwnM((blk, (ofs + k)%Z) |-> [v'])) ** ((OwnM((blk, (ofs + k)%Z) |-> [v]) -* OwnM((blk, ofs) |-> l'))).
  Proof.
    revert blk ofs k v l' GET. induction l; ss; i.
    { destruct k; ss. }
    destruct k; ss.
    { clarify. iIntros "H". rewrite points_to_split.
      iDestruct "H" as "[H0 H1]". iSplitL "H0".
      { rewrite Z.add_0_r. iExists _. ss. }
      iIntros "H". iEval (rewrite points_to_split). iSplitL "H".
      { rewrite Z.add_0_r. ss. }
      { ss. }
    }
    { iIntros "H". rewrite points_to_split.
      iDestruct "H" as "[H0 H1]".
      unfold option_map in GET. des_ifs.
      iPoseProof (IHl with "H1") as "H1"; eauto.
      iDestruct "H1" as "[H1 H2]". iDestruct "H1" as (v') "H1".
      replace (ofs + Z.pos (Pos.of_succ_nat k))%Z with (ofs + 1 + k)%Z by lia.
      iSplitL "H1"; auto. iIntros "H1".
      iEval (rewrite points_to_split). iSplitL "H0"; auto.
      iApply "H2". auto.
    }
  Qed.

  Lemma set_nth_map A B (f: A -> B) k l v
    :
    set_nth k (List.map f l) (f v) = option_map (List.map f) (set_nth k l v).
  Proof.
    revert k v. induction l; ss; i.
    { destruct k; ss. }
    { destruct k; ss. rewrite IHl. unfold option_map. des_ifs. }
  Qed.

  Lemma nth_error_map A B (f: A -> B) k l
    :
    nth_error (List.map f l) k = option_map f (nth_error l k).
  Proof.
    revert k. induction l; ss; i.
    { destruct k; ss. }
    { destruct k; ss. }
  Qed.

  Lemma repeat_nth A (a: A) n k
        (RANGE: k < n)
    :
    nth_error (List.repeat a n) k = Some a.
  Proof.
    revert k RANGE. induction n; ss; i.
    { lia. }
    { destruct k; ss. rewrite IHn; eauto. lia. }
  Qed.

  Lemma set_nth_length A k (a: A) l l'
        (SET: set_nth k l a = Some l')
    :
    length l' = length l.
  Proof.
    revert l l' SET. induction k; ss; i.
    { destruct l; ss. clarify. }
    { destruct l; ss. unfold option_map in *. des_ifs.
      ss. f_equal. eauto.
    }
  Qed.

  Lemma set_nth_error A k (a: A) l l' k'
        (SET: set_nth k l a = Some l')
    :
    nth_error l' k' = if Nat.eq_dec k' k then Some a else nth_error l k'.
  Proof.
    revert a l l' k' SET. induction k; ss; i.
    { destruct l; ss. clarify. des_ifs. destruct k'; ss. }
    { destruct l; ss. unfold option_map in *. des_ifs; ss.
      { erewrite IHk; eauto. des_ifs. }
      { destruct k'; ss. erewrite IHk; eauto. des_ifs. }
    }
  Qed.

  Theorem correct: refines2 [MapI0.Map] [MapM.Map GlobalStbM].
  Proof.
    eapply adequacy_local2. econs; ss. i. rr.
    econstructor 1 with (wf:=wf) (le:=inv_le top2); ss; et; cycle 2.
    { eexists (inl tt). rr. econs; ss. eapply to_semantic. iIntros "_". iRight. auto. }
    { eapply inv_le_PreOrder. ss. }
    econs; ss.
    { unfold MapI0.initF, MapM.initF, ccallU. init. iarg. mDesAll. subst.
      mDesOr "INV".
      { mDesAll. subst. mAssertPure False; ss. iApply (pending0_unique with "A1 A"). }
      mDesAll. subst. steps. astart 100. acatch.
      { eapply STBINCLM. stb_tac. ss. }
      icall_open _ with "".
      { iModIntro. instantiate (1:=Some _). ss. }
      { ss. }
      ss. mDesAll. subst. steps. astop. steps.
      iret _; ss.
      iModIntro. iSplit.
      { iLeft. iSplits. iSplitR "A"; eauto. iSplit; eauto.
        { iPureIntro. esplits; eauto.
          { instantiate (1:=List.repeat 0%Z (Z.to_nat x)). eapply repeat_length. }
          { i. rewrite repeat_nth; auto. lia. }
        }
        admit "malloc -> calloc".
      }
      { iSplits; eauto. }
    }
    econs; ss.
    { unfold MapI0.getF, MapM.getF, ccallU. init. iarg. mDesAll. subst.
      mDesOr "INV".
      2:{ mDesAll. subst. steps. exfalso. lia. }
      mDesAll. des. steps. unfold scale_int. des_ifs.
      2:{ exfalso. eapply n. eapply Z.divide_factor_r. }
      steps. astart 1. acatch.
      { eapply STBINCLM. stb_tac. ss. }
      mApply points_to_get_split "A1".
      2:{ eapply map_nth_error. eauto. }
      mDesAll.
      replace ((a0 + (z * 8) `div` 8)%Z) with ((a0 + Z.to_nat z)%Z); auto.
      2:{ rewrite Z_div_mult; ss. lia. }
      icall_open _ with "A1".
      { iModIntro. instantiate (1:=Some (_, _, _)). ss. iSplit; eauto. }
      { ss. }
      ss. mDesAll. subst. steps. astop. steps.
      iret _; ss. iModIntro. iSplit; ss.
      iLeft. iExists _. iExists _, _, _, _. iSplitR "A"; eauto.
      iSplit; eauto. iApply "A2". auto.
    }
    econs; ss.
    { unfold MapI0.setF, MapM.setF, ccallU. init. iarg. mDesAll. subst.
      mDesOr "INV".
      2:{ mDesAll. subst. steps. exfalso. lia. }
      mDesAll. des. steps. unfold scale_int. des_ifs.
      2:{ exfalso. eapply n. eapply Z.divide_factor_r. }
      steps. astart 1. acatch.
      { eapply STBINCLM. stb_tac. ss. }
      hexploit set_nth_success.
      { rewrite PURE0. instantiate (1:=Z.to_nat z). lia. }
      i. des.
      mApply points_to_set_split "A1".
      2:{ rewrite set_nth_map. rewrite H1. ss. }
      mDesAll.
      replace ((a0 + (z * 8) `div` 8)%Z) with ((a0 + Z.to_nat z)%Z); auto.
      2:{ rewrite Z_div_mult; ss. lia. }
      icall_open _ with "A1".
      { iModIntro. instantiate (1:=Some (_, _, _)). ss. iExists _. iSplit; eauto. }
      { ss. }
      ss. mDesAll. subst. steps. astop. steps.
      iret _; ss. iModIntro. iSplit; ss.
      iLeft. iExists _. iExists _, _, _, _. iSplitR "A"; eauto.
      iSplit; eauto.
      2:{ iApply "A2". eauto. }
      { iPureIntro. esplits; eauto.
        { erewrite set_nth_length; eauto. }
        { i. ss. erewrite set_nth_error; eauto. des_ifs; eauto. exfalso. lia. }
      }
    }
    econs; ss.
    { unfold MapI0.set_by_userF, MapM.set_by_userF, ccallU.
      init. iarg. mDesAll. subst. steps.
      rewrite STB_setM. steps.
      icall_weaken set_specM _ _ with "*".
      { refl. }
      { iModIntro. eauto. }
      { ss. }
      steps. mDesAll. subst. rewrite _UNWRAPU2. steps.
      iret _; ss. iModIntro. iSplit; ss.
    }
    Unshelve. all: ss.
  Qed.
End SIMMODSEM.
