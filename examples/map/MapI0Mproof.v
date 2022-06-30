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
             ((∃ blk ofs l, ⌜st_src = l↑ /\ st_tgt = (Vptr blk ofs)↑⌝ ** OwnM ((blk, ofs) |-> (List.map Vint l)) ** pending0) ∨ (⌜st_src = ([]: list Z)↑⌝))%I)
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).

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

  Ltac acatch :=
    match goal with
    | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn ?args) >>= _)) ] =>
      astep fn (tt↑)
    end.

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

  Theorem correct: refines2 [MapI0.Map] [MapM.Map GlobalStb].
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
      { eapply STBINCL. stb_tac. ss. }
      icall_open _ with "".
      { iModIntro. instantiate (1:=Some _). ss. iPureIntro.
        splits; ss. admit "add range condition".
      }
      { ss. }
      ss. mDesAll. subst. steps. astop. steps.
      iret _; ss.
      iModIntro. iSplit.
      { iLeft. iSplits. iSplitR "A"; eauto. iSplit; eauto.
        admit "malloc -> calloc".
      }
      { iSplits; eauto. }
    }
    econs; ss.
    { unfold MapI0.setF, MapM.setF, ccallU. init. iarg. mDesAll. subst.
      mDesOr "INV".
      2:{ mDesAll. subst. steps. exfalso. des_ifs. }
      mDesAll. des. steps. unfold scale_int. des_ifs.
      2:{ admit "add int allignment condition". }
      steps. astart 1. acatch.
      { eapply STBINCL. stb_tac. ss. }
      mApply points_to_set_split "A1".
      2:{ rewrite set_nth_map. rewrite _UNWRAPU0. ss. }
      mDesAll.
      icall_open _ with "A1".
      { iModIntro. instantiate (1:=Some (_, _, _)). ss.
        iExists _. iSplit; eauto.
        instantiate (1:=a2). admit "alignment".
      }
      { ss. }
      ss. mDesAll. subst. steps. astop. steps.
      iret _; ss. iModIntro. iSplit; ss.
      iLeft. iExists _. iExists _, _. iSplitR "A"; eauto.
      iSplit; eauto. iApply "A2". admit "alignment".
    }
    econs; ss.
    { unfold MapI0.getF, MapM.getF, ccallU. init. iarg. mDesAll. subst.
      mDesOr "INV".
      2:{ mDesAll. subst. steps. exfalso. destruct (Z.to_nat z); ss. }
      mDesAll. des. steps. unfold scale_int. des_ifs.
      2:{ admit "add int allignment condition". }
      steps. astart 1. acatch.
      { eapply STBINCL. stb_tac. ss. }
      mApply points_to_get_split "A1".
      2:{ eapply map_nth_error. eauto. }
      mDesAll.
      icall_open _ with "A1".
      { iModIntro. instantiate (1:=Some (_, _, _)). ss.
        iSplit; eauto. instantiate (1:=Vint z0). admit "alignment".
      }
      { ss. }
      ss. mDesAll. subst. steps. astop. steps.
      iret _; ss. iModIntro. iSplit; ss.
      iLeft. iExists _. iExists _, _. iSplitR "A"; eauto.
      iSplit; eauto. iApply "A2". admit "alignment".
    }
    Unshelve. all: ss.
  Qed.
End SIMMODSEM.
