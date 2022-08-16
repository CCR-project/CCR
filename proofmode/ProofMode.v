Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import PCM.
Require Import Any.
Require Import ITreelib.
Require Import AList.
Require Import Coq.Init.Decimal.
Require Export IPM.

Section ILIST.
  Context `{Σ: GRA.t}.

  Definition iPropL := alist string iProp.

  Fixpoint from_iPropL (l: iPropL): iProp :=
    match l with
    | [] => (emp)%I
    | (_, Phd)::Ptl => Phd ** (from_iPropL Ptl)
    end.

  Fixpoint get_ipm_pat (l: iPropL): string :=
    match l with
    | [] => "_"
    | (Hn, _) :: tl =>
      append "[" (append Hn (append " " (append (get_ipm_pat tl) "]")))
    end.

  Fixpoint is_fresh_name (Hn: string) (l: iPropL): bool :=
    match l with
    | [] => true
    | (Hn', _)::tl =>
      match String.eqb Hn Hn' with
      | true => false
      | false => is_fresh_name Hn tl
      end
    end.

  Fixpoint uint_to_string (n: uint) (acc: string): string :=
    match n with
    | Nil => acc
    | D0 tl => uint_to_string tl (append "0" acc)
    | D1 tl => uint_to_string tl (append "1" acc)
    | D2 tl => uint_to_string tl (append "2" acc)
    | D3 tl => uint_to_string tl (append "3" acc)
    | D4 tl => uint_to_string tl (append "4" acc)
    | D5 tl => uint_to_string tl (append "5" acc)
    | D6 tl => uint_to_string tl (append "6" acc)
    | D7 tl => uint_to_string tl (append "7" acc)
    | D8 tl => uint_to_string tl (append "8" acc)
    | D9 tl => uint_to_string tl (append "9" acc)
    end.

  Definition nat_to_string :=
    (fun n => uint_to_string (Nat.to_little_uint n Nil) "").

  Fixpoint get_fresh_name'
           (base: string) (n: nat) (fuel: nat) (l: iPropL): string :=
    match fuel with
    | 0 => "TMP"
    | S fuel' =>
      let Hn := append base (nat_to_string n) in
      if is_fresh_name Hn l
      then Hn
      else get_fresh_name' base (S n) fuel' l
    end.

  Definition get_fresh_name (base: string) (l: iPropL): string :=
    if is_fresh_name base l
    then base
    else get_fresh_name' base 0 100 l.

  Lemma iPropL_clear (Hn: string) (l: iPropL)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_remove Hn l).
  Proof.
    induction l; ss.
    { iIntros "H". iModIntro. iFrame. }
    { destruct a. iIntros "[H0 H1]". rewrite eq_rel_dec_correct. des_ifs; ss.
      { iPoseProof (IHl with "H1") as "> H1".
        iModIntro. iFrame. }
      { iPoseProof (IHl with "H1") as "> H1".
        iClear "H0". iModIntro. iFrame. }
    }
  Qed.

  Lemma iPropL_find_remove (Hn: string) (l: iPropL) P
        (FIND: alist_find Hn l = Some P)
    :
      from_iPropL l -∗ #=> (P ** from_iPropL (alist_remove Hn l)).
  Proof.
    revert P FIND. induction l; ss. i.
    destruct a. iIntros "[H0 H1]".
    rewrite eq_rel_dec_correct in *. des_ifs; ss.
    { iPoseProof (IHl with "H1") as "> H1"; et.
      iModIntro. iFrame. iFrame. }
    { iFrame. iApply iPropL_clear. iFrame. }
  Qed.

  Lemma iPropL_one Hn (l: iPropL) (P: iProp)
        (FIND: alist_find Hn l = Some P)
    :
      from_iPropL l -∗ #=> P.
  Proof.
    iIntros "H". iPoseProof (iPropL_find_remove with "H") as "> [H0 H1]"; et.
  Qed.

  Lemma iPropL_init (Hn: string) (P: iProp)
    :
      P -∗ from_iPropL [(Hn, P)].
  Proof.
    ss. iIntros "H". iFrame.
  Qed.

  Lemma iPropL_uentail Hn (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn l = Some P0)
        (ENTAIL: P0 -∗ #=> P1)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn P1 l).
  Proof.
    revert P0 P1 FIND ENTAIL. induction l; ss. i.
    destruct a. iIntros "[H0 H1]".
    rewrite eq_rel_dec_correct in *. des_ifs.
    { ss. iPoseProof (IHl with "H1") as "H1"; et. repeat iFrame. }
    { ss. iPoseProof (ENTAIL with "H0") as "> H0".
      iPoseProof (iPropL_clear with "H1") as "> H1".
      iModIntro. iFrame. }
  Qed.

  Lemma iPropL_entail Hn (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn l = Some P0)
        (ENTAIL: P0 -∗ P1)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn P1 l).
  Proof.
    eapply iPropL_uentail; et. iIntros "H".
    iPoseProof (ENTAIL with "H") as "H". iModIntro. iFrame.
  Qed.

  Lemma iPropL_upd Hn (l: iPropL) (P: iProp)
        (FIND: alist_find Hn l = Some (#=> P))
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn P l).
  Proof.
    hexploit (@iPropL_uentail Hn l (#=> P) P); et.
  Qed.

  Lemma iPropL_destruct_ex Hn (l: iPropL) A (P: A -> iProp)
        (FIND: alist_find Hn l = Some (∃ (a: A), P a)%I)
    :
      from_iPropL l -∗ ∃ (a: A), #=> from_iPropL (alist_add Hn (P a) l).
  Proof.
    revert FIND. induction l; ss. i.
    destruct a. iIntros "[H0 H1]".
    rewrite eq_rel_dec_correct in *. des_ifs; ss.
    { iPoseProof (IHl with "H1") as (a) "H1"; et.
      iExists a. repeat iFrame. }
    { iDestruct "H0" as (a) "H0". iExists a.
      iFrame. iApply iPropL_clear. iFrame. }
  Qed.

  Lemma iPropL_destruct_or Hn (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn l = Some (P0 ∨ P1)%I)
    :
      from_iPropL l -∗ (#=> from_iPropL (alist_add Hn P0 l)) ∨ #=> from_iPropL (alist_add Hn P1 l).
  Proof.
    revert FIND. induction l; ss. i.
    destruct a. iIntros "[H0 H1]".
    rewrite eq_rel_dec_correct in *. des_ifs; ss.
    { iPoseProof (IHl with "H1") as "[H1|H1]"; et.
      { iLeft. repeat iFrame. }
      { iRight. repeat iFrame. }
    }
    { iDestruct "H0" as "[H0|H0]".
      { iLeft. iFrame. iApply iPropL_clear. iFrame. }
      { iRight. iFrame. iApply iPropL_clear. iFrame. }
    }
  Qed.

  Lemma iPropL_add (Hn: string) (l: iPropL) P
    :
      P ** from_iPropL l -∗ #=> (from_iPropL (alist_add Hn P l)).
  Proof.
    unfold alist_add. ss. iIntros "[H0 H1]".
    iFrame. iApply iPropL_clear. iFrame.
  Qed.

  Lemma iPropL_destruct_sep Hn_old Hn_new0 Hn_new1 (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn_old l = Some (P0 ** P1))
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn_new1 P1 (alist_add Hn_new0 P0 (alist_remove Hn_old l))).
  Proof.
    iIntros "H".
    iPoseProof (iPropL_find_remove with "H") as "> [H0 H1]"; et.
    iDestruct "H0" as "[H0 H2]". iCombine "H0 H1" as "H0".
    iPoseProof (iPropL_add with "H0") as "> H".
    iApply iPropL_add. iFrame.
  Qed.

  Lemma iPropL_alist_pop Hn P (l0 l1: iPropL)
        (FIND: alist_pop Hn l0 = Some (P, l1))
    :
      from_iPropL l0 ⊢ P ** from_iPropL l1.
  Proof.
    revert P l1 FIND. induction l0; ss. i.
    destruct a. rewrite eq_rel_dec_correct in *. des_ifs.
    ss. hexploit IHl0; et. i.
    iIntros "[H0 H1]". iFrame. iApply H. iFrame.
  Qed.

  Lemma iPropL_alist_pops l Hns
    :
      from_iPropL l ⊢ from_iPropL (fst (alist_pops Hns l)) ** from_iPropL (snd (alist_pops Hns l)).
  Proof.
    induction Hns. ss.
    { iIntros "H0". iFrame. }
    { ss. des_ifs. ss. etrans; et.
      iIntros "[H0 H1]". iFrame.
      iApply iPropL_alist_pop; et. }
  Qed.

  Lemma iPropL_assert (Hns: list string) (Hn_new: string) (l: iPropL) (P: iProp)
        (FIND: from_iPropL (fst (alist_pops Hns l)) -∗ P)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn_new P (snd (alist_pops Hns l))).
  Proof.
    iIntros "H". iPoseProof (iPropL_alist_pops with "H") as "[H0 H1]".
    iPoseProof (FIND with "H0") as "H0".
    iApply iPropL_add. iFrame.
  Qed.

  Fixpoint parse_hyps (b: bool) (k: string -> string) (Hns: string): list string :=
    match Hns with
    | EmptyString => if b then [k ""] else []
    | String (Ascii.Ascii false false false false false true false false) tl =>
      (k "") :: parse_hyps false id tl
    | String c tl =>
      parse_hyps true (fun str => k (String c str)) tl
    end.

  Definition parse_hyps_complete (Hns: string): (bool * list string) :=
    match Hns with
    | EmptyString => (true, [])
    | "*" => (false, [])
    | String (Ascii.Ascii true false true true false true false false)
             (String (Ascii.Ascii false false false false false true false false)
                     tl) => (false, parse_hyps true id tl)
    | String (Ascii.Ascii true false true true false true false false)
             tl => (false, parse_hyps true id tl)
    | _ => (true, parse_hyps true id Hns)
    end.

  Definition list_compl (l0 l1: list string): list string :=
    List.filter (fun str0 => forallb (fun str1 => negb (beq_str str0 str1)) l0) l1.
End ILIST.
Arguments from_iPropL: simpl never.

Ltac start_ipm_proof :=
  match goal with
  | |- from_iPropL ?l -∗ _ =>
    let pat := (eval simpl in (get_ipm_pat l)) in
    simpl; iIntros pat
  | _ => try unfold from_iPropL
  end.

Section CURRENT.
  Context `{Σ: GRA.t}.

  Variant current_iProp (fmr: Σ) (I: iProp): Prop :=
  | current_iProp_intro
      r
      (IPROP: I r)
      (GWF: URA.wf fmr)
      (UPD: URA.updatable fmr r)
  .

  Lemma current_iProp_entail I1 fmr I0
        (ACC: current_iProp fmr I0)
        (UPD: I0 ⊢ I1)
    :
      current_iProp fmr I1.
  Proof.
    inv ACC. econs; et.
    uipropall. eapply UPD; et. eapply URA.updatable_wf; et.
  Qed.

  Lemma current_iProp_pure P fmr
        (ACC: current_iProp fmr (⌜P⌝)%I)
    :
      P.
  Proof.
    inv ACC. rr in IPROP. uipropall.
  Qed.

  Lemma current_iProp_ex fmr A (P: A -> iProp)
        (ACC: current_iProp fmr (bi_exist P))
    :
      exists x, current_iProp fmr (P x).
  Proof.
    inv ACC. rr in IPROP. uipropall.
    des. exists x. econs; et.
  Qed.

  Lemma current_iProp_or fmr I0 I1
        (ACC: current_iProp fmr (I0 ∨ I1)%I)
    :
      current_iProp fmr I0 \/ current_iProp fmr I1.
  Proof.
    inv ACC. uipropall. des.
    { left. econs; et. }
    { right. econs; et. }
  Qed.

  Lemma current_iProp_upd fmr I
        (ACC: current_iProp fmr (#=> I))
    :
      current_iProp fmr I.
  Proof.
    inv ACC. uipropall. des. econs; et. etrans; et.
  Qed.

  Lemma current_iProp_own fmr (M: URA.t) `{@GRA.inG M Σ} (m: M)
        (ACC: current_iProp fmr (OwnM m))
    :
      URA.wf m.
  Proof.
    unfold OwnM in *.
    inv ACC. uipropall. unfold URA.extends in *. des. subst.
    eapply GRA.embed_wf; et.
    eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable. exists ctx; r_solve.
  Qed.
End CURRENT.



Section TACTICS.
  Context `{Σ: GRA.t}.

  Definition current_iPropL (fmr: Σ) (l: iPropL) :=
    current_iProp fmr (from_iPropL l).

  Lemma current_iPropL_pure Hn fmr (l: iPropL) (P: Prop)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn l = Some (⌜P⌝)%I)
    :
      current_iPropL fmr (alist_remove Hn l) /\ P.
  Proof.
    split.
    - eapply current_iProp_upd.
      eapply current_iProp_entail; et.
      eapply iPropL_clear.
    - eapply current_iProp_pure.
      eapply current_iProp_upd.
      eapply current_iProp_entail; et.
      eapply iPropL_one; et.
  Qed.

  Lemma current_iPropL_destruct_ex Hn fmr (l: iPropL) A (P: A -> iProp)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn l = Some (bi_exist P))
    :
      exists (a: A), current_iPropL fmr (alist_add Hn (P a) l).
  Proof.
    eapply current_iProp_entail in ACC.
    2: { eapply iPropL_destruct_ex; et. }
    eapply current_iProp_ex in ACC. des.
    exists x. eapply current_iProp_upd. et.
  Qed.

  Lemma current_iPropL_destruct_or Hn fmr (l: iPropL) (P0 P1: iProp)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn l = Some (P0 ∨ P1)%I)
    :
      current_iPropL fmr (alist_add Hn P0 l) \/
      current_iPropL fmr (alist_add Hn P1 l).
  Proof.
    eapply current_iProp_entail in ACC.
    2: { eapply iPropL_destruct_or; et. }
    eapply current_iProp_or in ACC. des.
    { left. eapply current_iProp_upd. et. }
    { right. eapply current_iProp_upd. et. }
  Qed.

  Lemma current_iPropL_destruct_sep Hn_old Hn_new0 Hn_new1 fmr (l: iPropL) (P0 P1: iProp)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn_old l = Some (P0 ** P1)%I)
    :
      current_iPropL fmr (alist_add Hn_new1 P1 (alist_add Hn_new0 P0 (alist_remove Hn_old l))).
  Proof.
    eapply current_iProp_upd.
    eapply current_iProp_entail; et.
    eapply iPropL_destruct_sep; et.
  Qed.

  Lemma current_iPropL_upd Hn fmr (l: iPropL) (P: iProp)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn l = Some (#=> P)%I)
    :
      current_iPropL fmr (alist_add Hn P l).
  Proof.
    eapply current_iProp_upd.
    eapply current_iProp_entail; et.
    eapply iPropL_upd; et.
  Qed.

  Lemma current_iPropL_own_wf Hn fmr (l: iPropL) M `{@GRA.inG M Σ} (m: M)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn l = Some (OwnM m))
    :
      URA.wf m.
  Proof.
    eapply current_iProp_own.
    eapply current_iProp_upd.
    eapply current_iProp_entail; et.
    eapply iPropL_one; et.
  Qed.

  Lemma current_iPropL_clear Hn fmr (l: iPropL)
        (ACC: current_iPropL fmr l)
    :
      current_iPropL fmr (alist_remove Hn l).
  Proof.
    eapply current_iProp_upd.
    eapply current_iProp_entail; et.
    eapply iPropL_clear; et.
  Qed.

  Lemma current_iPropL_assert Hns Hn_new (P: iProp) fmr (l: iPropL)
        (ACC: current_iPropL fmr l)
        (FIND: from_iPropL (fst (alist_pops Hns l)) -∗ P)
    :
      current_iPropL fmr (alist_add Hn_new P (snd (alist_pops Hns l))).
  Proof.
    eapply current_iProp_upd.
    eapply current_iProp_entail; et.
    eapply iPropL_assert; et.
  Qed.

  Lemma current_iPropL_assert_pure (P: Prop) fmr (l: iPropL)
        (ACC: current_iPropL fmr l)
        (FIND: from_iPropL l -∗ ⌜P⌝)
    :
      P.
  Proof.
    eapply current_iProp_pure.
    eapply current_iProp_entail; et.
  Qed.

  Lemma current_iPropL_entail Hn fmr (l: iPropL) (P0 P1: iProp)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn l = Some P0)
        (ENTAIL: P0 -∗ P1)
    :
      current_iPropL fmr (alist_add Hn P1 l).
  Proof.
    eapply current_iProp_upd.
    eapply current_iProp_entail; et.
    eapply iPropL_entail; et.
  Qed.

  Lemma current_iPropL_univ Hn A a fmr (l: iPropL) (P: A -> iProp)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn l = Some (bi_forall P))
    :
      current_iPropL fmr (alist_add Hn (P a) l).
  Proof.
    eapply current_iPropL_entail; et.
    iIntros "H".
    (* TODO which IPM tactic? *)
    iApply bi.forall_elim. ss.
  Qed.

  Lemma current_iPropL_wand Hn0 Hn1 fmr (l l0 l1: iPropL)
        (P0 P1: iProp)
        (ACC: current_iPropL fmr l)
        (FIND0: alist_pop Hn0 l = Some ((P0 -∗ P1)%I, l0))
        (FIND1: alist_pop Hn1 l0 = Some (P0, l1))
    :
      current_iPropL fmr (alist_add Hn0 P1 l1).
  Proof.
    exploit (@current_iPropL_assert [Hn1; Hn0] Hn0 P1); et.
    { ss. rewrite FIND0. rewrite FIND1. ss.
      iIntros "[H0 [H1 _]]". iApply "H1". iApply "H0". }
    ss. rewrite FIND0. rewrite FIND1. ss.
  Qed.

  Lemma current_iPropL_destruct_and_l Hn fmr (l: iPropL) (P0 P1: iProp)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn l = Some (P0 ∧ P1)%I)
    :
      current_iPropL fmr (alist_add Hn P0 l).
  Proof.
    eapply current_iPropL_entail; et.
    iIntros "H". iDestruct "H" as "[H _]". iApply "H".
  Qed.

  Lemma current_iPropL_destruct_and_r Hn fmr (l: iPropL) (P0 P1: iProp)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn l = Some (P0 ∧ P1)%I)
    :
      current_iPropL fmr (alist_add Hn P1 l).
  Proof.
    eapply current_iPropL_entail; et.
    iIntros "H". iDestruct "H" as "[_ H]". iApply "H".
  Qed.

  Lemma list_filter_idemp A f (l: list A):
    List.filter f (List.filter f l) = List.filter f l.
  Proof.
    induction l; ss. des_ifs. ss. des_ifs. f_equal; auto.
  Qed.

  Lemma current_iPropL_destruct_sep' Hn_old Hn_new0 Hn_new1 fmr (l: iPropL) (P0 P1 P2: iProp)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn_old l = Some P2)
        (ENTAIL: P2 -∗ (P0 ** P1)%I)
    :
      current_iPropL fmr (alist_add Hn_new1 P1 (alist_add Hn_new0 P0 (alist_remove Hn_old l))).
  Proof.
    eapply current_iPropL_entail in ACC; et.
    eapply (@current_iPropL_destruct_sep Hn_old Hn_new0 Hn_new1 _ _ P0 P1) in ACC; et.
    { match goal with
      | [H: current_iPropL _ ?l0 |- current_iPropL _ ?l1] => replace l1 with l0
      end; auto.
      f_equal. f_equal. clear. unfold alist_add, alist_remove. ss.
      rewrite eq_rel_dec_correct. des_ifs. eapply list_filter_idemp.
    }
    { unfold alist_add, alist_remove. ss.
      rewrite eq_rel_dec_correct. des_ifs. }
  Qed.

  Lemma current_iPropL_destruct_and_pure_l
        Hn_old Hn_new0 Hn_new1 fmr (l: iPropL) (P0: Prop) (P1: iProp)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn_old l = Some ((⌜P0⌝) ∧ P1)%I)
    :
      current_iPropL fmr (alist_add Hn_new1 P1 (alist_add Hn_new0 (⌜P0⌝)%I (alist_remove Hn_old l))).
  Proof.
    eapply current_iPropL_destruct_sep'; et.
    iIntros "H". iDestruct "H" as "[H0 H1]". iFrame.
  Qed.

  Lemma current_iPropL_destruct_and_pure_r
        Hn_old Hn_new0 Hn_new1 fmr (l: iPropL) (P0: iProp) (P1: Prop)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn_old l = Some (P0 ∧ (⌜P1⌝))%I)
    :
      current_iPropL fmr (alist_add Hn_new1 (⌜P1⌝)%I (alist_add Hn_new0 P0 (alist_remove Hn_old l))).
  Proof.
    eapply current_iPropL_destruct_sep'; et.
    iIntros "H". iDestruct "H" as "[H0 H1]". iFrame.
  Qed.

  Lemma current_iPropL_destruct_own Hn_old Hn_new0 Hn_new1
        fmr (l: iPropL) M `{@GRA.inG M Σ} (m0 m1: M)
        (ACC: current_iPropL fmr l)
        (FIND: alist_find Hn_old l = Some (OwnM (URA.add m0 m1)))
    :
      current_iPropL fmr (alist_add Hn_new1 (OwnM m1) (alist_add Hn_new0 (OwnM m0) (alist_remove Hn_old l))).
  Proof.
    eapply current_iPropL_destruct_sep'; et.
    iIntros "[H0 H1]". iFrame.
  Qed.

  Lemma current_iPropL_merge_own Hn0 Hn1 fmr (l l0 l1: iPropL)
        M `{@GRA.inG M Σ} (m0 m1: M)
        (ACC: current_iPropL fmr l)
        (FIND0: alist_pop Hn0 l = Some (OwnM m0, l0))
        (FIND1: alist_pop Hn1 l0 = Some (OwnM m1, l1))
    :
      current_iPropL fmr (alist_add Hn0 (OwnM (URA.add m0 m1)) l1).
  Proof.
    exploit (@current_iPropL_assert [Hn1; Hn0] Hn0 (OwnM (URA.add m0 m1))); et.
    { ss. rewrite FIND0. rewrite FIND1. ss.
      iIntros "[H0 [H1 _]]". iSplitL "H1"; iFrame. }
    ss. rewrite FIND0. rewrite FIND1. ss.
  Qed.
End TACTICS.
Arguments current_iPropL: simpl never.

Section INW.
  Context `{Σ: GRA.t}.
  Definition iNW (name: string) (P: iProp'): iProp' := P.
End INW.
Hint Unfold iNW.

Notation "☀----IPROPS----☀ fmr" := (@current_iPropL _ fmr)
                                 (at level 2,
                                  format "☀----IPROPS----☀  fmr '//'",
                                  only printing).

Notation "P .. Q" :=
  (@cons (prod string (bi_car iProp)) Q .. (@cons (prod string (bi_car iProp)) P nil) ..)
    (at level 1,
     P at level 200,
     format "'[' P '//' .. '//' Q ']'",
     only printing,
     left associativity).

Ltac on_current TAC :=
  match goal with
  | ACC: @current_iPropL _ _ _ |- _ => TAC ACC
  end.

Ltac get_fresh_name_tac Hn :=
  match goal with
  | _: @current_iPropL _ _ ?l |- _ =>
    let H := (eval compute in (get_fresh_name Hn l)) in
    constr:(H)
  end.

Ltac select_ihyps Hns :=
  let pat := (eval simpl in (parse_hyps_complete Hns)) in
  match pat with
  | (true, ?l0) => constr:(l0)
  | (false, ?l0) =>
    match goal with
    | ACC: @current_iPropL _ _ ?l1 |- _ =>
      eval simpl in (list_compl l0 (List.map fst l1))
    end
  end.

Tactic Notation "mPure'" uconstr(Hn) "as" simple_intropattern(pat)
  := on_current ltac:(fun H =>
                        eapply (@current_iPropL_pure _ Hn) in H;
                        [|asimpl; reflexivity];
                        destruct H as [H pat];
                        asimpl in H).

Tactic Notation "mPure" uconstr(Hn) "as" simple_intropattern(pat) :=
  mPure' Hn as pat.

Tactic Notation "mPure" uconstr(Hn) :=
  let PURE := fresh "PURE" in
  mPure' Hn as PURE.

Ltac mDesEx' Hn a := on_current ltac:(fun H =>
                                        eapply (@current_iPropL_destruct_ex _ Hn) in H;
                                        [|asimpl; reflexivity];
                                        destruct H as [a H];
                                        asimpl in H).

Tactic Notation "mDesEx" constr(Hn) "as" ident(a) :=
  mDesEx' Hn a.

Tactic Notation "mDesEx" constr(Hn) :=
  let a := fresh "a" in
  mDesEx' Hn a.

Ltac mDesOr Hn := on_current ltac:(fun H =>
                                     eapply (@current_iPropL_destruct_or _ Hn) in H;
                                     [|asimpl; reflexivity];
                                     destruct H as [H|H];
                                     asimpl in H).

Ltac mDesSep' Hn_old Hn_new0 Hn_new1 :=
  on_current ltac:(fun H =>
                     eapply (@current_iPropL_destruct_sep _ Hn_old Hn_new0 Hn_new1) in H;
                     [|asimpl; reflexivity];
                     asimpl in H).

Tactic Notation "mDesSep" constr(Hn_old) "as" constr(Hn_new0) constr(Hn_new1) :=
  mDesSep' Hn_old Hn_new0 Hn_new1.

Tactic Notation "mDesSep" constr(Hn_old) :=
  let Hn_new1 := get_fresh_name_tac "A" in
  mDesSep' Hn_old Hn_old Hn_new1.

Ltac mUpd Hn := on_current ltac:(fun H =>
                                   eapply (@current_iPropL_upd _ Hn) in H;
                                   [|asimpl; reflexivity];
                                   asimpl in H).

Ltac mOwnWf' Hn WF := on_current ltac:(fun H =>
                                         pose proof H as WF;
                                         eapply (@current_iPropL_own_wf _ Hn) in WF;
                                         [|asimpl; reflexivity];
                                         asimpl in H).

Tactic Notation "mOwnWf" constr(Hn) "as" ident(WF) :=
  mOwnWf' Hn WF.

Tactic Notation "mOwnWf" constr(Hn) :=
  let WF := fresh "WF" in
  mOwnWf' Hn WF.

Ltac mClear Hn := on_current ltac:(fun H =>
                                     eapply (@current_iPropL_clear _ Hn) in H;
                                     asimpl in H).

Tactic Notation "mAssert'" uconstr(P) uconstr(Hns) constr(Hn_new) :=
  let Hns := select_ihyps Hns in
  on_current ltac:(fun H =>
                     eapply (@current_iPropL_assert _ Hns Hn_new P) in H;
                     cycle 1;
                     [start_ipm_proof|asimpl in H]).

Tactic Notation "mAssert" uconstr(P) "with" uconstr(Hns) "as" constr(Hn_new) :=
  mAssert' P Hns Hn_new.

Tactic Notation "mAssert" uconstr(P) "with" uconstr(Hns) :=
  let Hn_new := get_fresh_name_tac "A" in
  mAssert' P Hns Hn_new.

Ltac mAssertPure' P PURE := on_current ltac:(fun H =>
                                               pose proof H as PURE;
                                               eapply (@current_iPropL_assert_pure _ P) in PURE;
                                               cycle 1;
                                               [clear PURE; start_ipm_proof|asimpl in H]).

Tactic Notation "mAssertPure" constr(P) "as" ident(PURE) :=
  mAssertPure' P PURE.

Tactic Notation "mAssertPure" constr(P) :=
  let PURE := fresh "PURE" in
  mAssertPure' P PURE.

Tactic Notation "mAssertPure" "_" "as" ident(PURE) :=
  let P := fresh "P" in
  evar (P: Prop);
  mAssertPure P as PURE;
  [subst P|subst P].

Tactic Notation "mAssertPure" "_" :=
  let PURE := fresh "PURE" in
  let P := fresh "P" in
  evar (P: Prop);
  mAssertPure P as PURE;
  [subst P|subst P].

Ltac mApply LEM Hn := on_current ltac:(fun H =>
                                         eapply (@current_iPropL_entail _ Hn) in H;
                                         [|asimpl in H; reflexivity|eapply LEM];
                                         asimpl in H).

Ltac mSpcUniv' Hn a := on_current ltac:(fun H =>
                                          eapply (@current_iPropL_univ _ Hn _ a) in H;
                                          [|asimpl; reflexivity];
                                          asimpl in H).

Tactic Notation "mSpcUniv" constr(Hn) "with" uconstr(a) :=
  mSpcUniv' Hn a.

Ltac mSpcWand' Hn0 Hn1 := on_current ltac:(fun H =>
                                             eapply (@current_iPropL_wand _ Hn0 Hn1) in H;
                                             [|asimpl; reflexivity|asimpl; reflexivity];
                                             asimpl in H).

Tactic Notation "mSpcWand" constr(Hn0) "with" constr(Hn1) :=
  mSpcWand' Hn0 Hn1.

Ltac mDesAndL Hn := on_current ltac:(fun H =>
                                       eapply (@current_iPropL_destruct_and_l _ Hn) in H;
                                       [|asimpl; reflexivity];
                                       asimpl in H).

Ltac mDesAndR Hn := on_current ltac:(fun H =>
                                       eapply (@current_iPropL_destruct_and_r _ Hn) in H;
                                       [|asimpl; reflexivity];
                                       asimpl in H).

Ltac mDesAndPureL' Hn_old Hn_new0 Hn_new1 :=
  on_current ltac:(fun H =>
                     eapply (@current_iPropL_destruct_and_pure_l _ Hn_old Hn_new0 Hn_new1) in H;
                     [|asimpl; reflexivity];
                     asimpl in H).

Tactic Notation "mDesAndPureL" constr(Hn_old) "as" constr(Hn_new0) constr(Hn_new1) :=
  mDesAndPureL' Hn_old Hn_new0 Hn_new1.

Tactic Notation "mDesAndPureL" constr(Hn_old) :=
  let Hn_new1 := get_fresh_name_tac "A" in
  mDesAndPureL' Hn_old Hn_new1 Hn_old.

Ltac mDesAndPureR' Hn_old Hn_new0 Hn_new1 :=
  on_current ltac:(fun H =>
                     eapply (@current_iPropL_destruct_and_pure_r _ Hn_old Hn_new0 Hn_new1) in H;
                     [|asimpl; reflexivity];
                     asimpl in H).

Tactic Notation "mDesAndPureR" constr(Hn_old) "as" constr(Hn_new0) constr(Hn_new1) :=
  mDesAndPureR' Hn_old Hn_new0 Hn_new1.

Tactic Notation "mDesAndPureR" constr(Hn_old) :=
  let Hn_new1 := get_fresh_name_tac "A" in
  mDesAndPureR' Hn_old Hn_old Hn_new1.

Ltac mDesOwn' Hn_old Hn_new0 Hn_new1 :=
  on_current ltac:(fun H =>
                     eapply (@current_iPropL_destruct_own _ Hn_old Hn_new0 Hn_new1) in H;
                     [|asimpl; reflexivity];
                     asimpl in H).

Tactic Notation "mDesOwn" constr(Hn_old) "as" constr(Hn_new0) constr(Hn_new1) :=
  mDesOwn' Hn_old Hn_new0 Hn_new1.

Tactic Notation "mDesOwn" constr(Hn_old) :=
  let Hn_new1 := get_fresh_name_tac "A" in
  mDesOwn' Hn_old Hn_old Hn_new1.

Ltac mCombine Hn0 Hn1 := on_current ltac:(fun H =>
                                            eapply (@current_iPropL_merge_own _ Hn0 Hn1) in H;
                                            [|asimpl; reflexivity|asimpl; reflexivity];
                                            asimpl in H).

Tactic Notation "mRed" "in" constr(Hn) :=
  on_current ltac:(fun H =>
                     match type of H with
                     | @current_iPropL _ _ ?l =>
                       match (eval simpl in (alist_find Hn l)) with
                       | Some ?v =>
                         let v := (eval simpl in v) in
                         let v' := (eval red in v) in
                         let l' := constr:(alist_replace Hn v' l) in
                         change l with l' in H;
                         asimpl in H
                       end
                     end).

Tactic Notation "mUnfold" constr(t) "in" constr(Hn) :=
  on_current ltac:(fun H =>
                     match type of H with
                     | @current_iPropL _ _ ?l =>
                       match (eval simpl in (alist_find Hn l)) with
                       | Some ?v =>
                         let v := (eval simpl in v) in
                         let v' := (eval unfold t in v) in
                         let l' := constr:(alist_replace Hn v' l) in
                         change l with l' in H;
                         asimpl in H
                       end
                     end).

Tactic Notation "mEval" tactic(tac) "in" constr(Hn) :=
  on_current ltac:(fun H =>
                     eapply (@current_iPropL_entail _ Hn) in H;
                     [|asimpl in H; reflexivity
                      |tac; refl];
                     asimpl in H).

Tactic Notation "mRename" constr(Hn_old) "into" constr(Hn_new) :=
  mAssert _ with Hn_old as Hn_new; [iExact Hn_old|].

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
    | @iNW _ ?Hn' ?x =>
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

Goal <<A: True>>. ss. Abort.
Notation "{{ x : t }}" := (@iNW _ x t) (at level 80, x at next level, t at next level, no associativity).
Goal <<A: True>>. ss. Abort.

Section TEST.
  Context {Σ: GRA.t}.
  Context {M: URA.t}.
  Context `{@GRA.inG M Σ}.

  Variable fmr: Σ.

  Notation "Hns 'TO' Hns'" := ((current_iPropL fmr Hns) -> (current_iPropL fmr Hns')) (at level 60).
  Ltac check := erewrite f_equal; [eassumption|refl].

  (* check tactic *)
  Goal ∀ X, [("A", X)] TO [("B", X)].
  Proof. i. mDesAll. Fail check. Abort.

  (* iNW *)
  (* Goal ∀ X, [("A", {{ "A" ; X }} )] TO [("A", X)]. *)
  Goal ∀ X, [("A", {{ "A" : X }} )] TO [("A", X)].
  Proof. i. mDesAll. check. Qed.

  Goal ∀ P Q X Y, [("A", {{"A": X}}); ("H", {{"B": P}} ** {{"C": Q}}); ("B", {{"D": Y}})]
                    TO
                    [("D", Y); ("B1", P); ("C", Q); ("A", X)].
  Proof. i. mDesAll. check. Qed.

  (* mDesSep *)
  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("A", X); ("H", P ** Q); ("B", Y)]),
      False.
  Proof.
    i. mDesSep "H".
  Abort.

  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("A", X); ("H", P ** Q); ("B", Y)]),
      False.
  Proof.
    i. mDesSep "H" as "H0" "H1".
  Abort.

  (* mDesOr *)
  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("A", X); ("H", (P ∨ Q)%I); ("B", Y)]),
      False.
  Proof.
    i. mDesOr "H".
  Abort.

  (* mPure *)
  Goal forall fr P X Y
              (ACC: current_iPropL fr [("A", X); ("H", (⌜P⌝)%I); ("B", Y)]),
      False.
  Proof.
    i. mPure "H".
  Abort.

  Goal forall fr P X Y
              (ACC: current_iPropL fr [("A", X); ("H", (⌜P⌝)%I); ("B", Y)]),
      False.
  Proof.
    i. mPure "H" as PURE.
  Abort.

  (* mDesEx *)
  Goal forall fr A P X Y
              (ACC: current_iPropL fr [("A", X); ("H", (∃ (a: A), P a)%I); ("B", Y)]),
      False.
  Proof.
    i. mDesEx "H" as a.
  Abort.

  Goal forall fr A P X Y
              (ACC: current_iPropL fr [("A", X); ("H", (∃ (a: A), P a)%I); ("B", Y)]),
      False.
  Proof.
    i. mDesEx "H".
  Abort.

  (* mUpd *)
  Goal forall fr P X Y
              (ACC: current_iPropL fr [("A", X); ("H", #=> P); ("B", Y)]),
      False.
  Proof.
    i. mUpd "H".
  Abort.

  (* mOwnWf *)
  Goal forall fr (m: M) X Y
              (ACC: current_iPropL fr [("A", X); ("H", OwnM m); ("B", Y)]),
      False.
  Proof.
    i. mOwnWf "H" as WF.
  Abort.

  Goal forall fr (m: M) X Y
              (ACC: current_iPropL fr [("A", X); ("H", OwnM m); ("B", Y)]),
      False.
  Proof.
    i. mOwnWf "H".
  Abort.

  (* mClear *)
  Goal forall fr P X Y
              (ACC: current_iPropL fr [("A", X); ("H", P); ("B", Y)]),
      False.
  Proof.
    i. mClear "H".
  Abort.

  (* mDesOwn *)
  Goal forall fr (m0 m1: M) X Y
              (ACC: current_iPropL fr [("A", X); ("H", OwnM (URA.add m0 m1)); ("B", Y)]),
      False.
  Proof.
    i. mDesOwn "H" as "H0" "H1".
  Abort.

  Goal forall fr (m0 m1: M) X Y
              (ACC: current_iPropL fr [("A", X); ("H", OwnM (URA.add m0 m1)); ("B", Y)]),
      False.
  Proof.
    i. mDesOwn "H".
  Abort.

  (* mCombine *)
  Goal forall fr (m0 m1: M) X Y
              (ACC: current_iPropL fr [("H1", OwnM (m1)); ("A", X); ("H0", OwnM (m0)); ("B", Y)]),
      False.
  Proof.
    i. mCombine "H0" "H1".
  Abort.

  (* mDesAndL *)
  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("A", X); ("H", (P ∧ Q)%I); ("B", Y)]),
      False.
  Proof.
    i. mDesAndL "H".
  Abort.

  (* mDesAndR *)
  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("A", X); ("H", (P ∧ Q)%I); ("B", Y)]),
      False.
  Proof.
    i. mDesAndR "H".
  Abort.

  (* mDesAndPureL *)
  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("A", X); ("H", ((⌜P⌝)%I ∧ Q)%I); ("B", Y)]),
      False.
  Proof.
    i. mDesAndPureL "H" as "H0" "H1".
  Abort.

  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("A", X); ("H", ((⌜P⌝)%I ∧ Q)%I); ("B", Y)]),
      False.
  Proof.
    i. mDesAndPureL "H".
  Abort.

  (* mDesAndPureR *)
  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("A", X); ("H", (P ∧ (⌜Q⌝)%I )%I); ("B", Y)]),
      False.
  Proof.
    i. mDesAndPureR "H" as "H0" "H1".
  Abort.

  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("A", X); ("H", (P ∧ (⌜Q⌝)%I )%I); ("B", Y)]),
      False.
  Proof.
    i. mDesAndPureR "H".
  Abort.

  (* mSpcUniv *)
  Goal forall fr P X Y
              (ACC: current_iPropL fr [("A", X); ("H", (∀ (n: nat), P n)%I); ("B", Y)]),
      False.
  Proof.
    i. mSpcUniv "H" with 3.
  Abort.

  (* mSpcWand *)
  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("H1", (P -∗ Q)%I); ("A", X); ("H0", P); ("B", Y)]),
      False.
  Proof.
    i. mSpcWand "H1" with "H0".
  Abort.

  (* mAssert *)
  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("H1", (P -∗ Q)%I); ("A", X); ("H0", P); ("B", Y)]),
      False.
  Proof.
    i. mAssert Q with "- A B" as "H0".
    { iApply "H1". iApply "H0". }
  Abort.

  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("H1", (P -∗ Q)%I); ("A", X); ("H0", P); ("B", Y)]),
      False.
  Proof.
    i. mAssert Q with "H0 H1".
    { iApply "H1". iApply "H0". }
  Abort.

  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("H1", (P -∗ Q)%I); ("A", X); ("H0", P); ("B", Y)]),
      False.
  Proof.
    i. mAssert _ with "H0 H1".
    { iSpecialize ("H1" with "H0"). iExact "H1". }
  Abort.

  Goal forall fr P Q X Y
              (ACC: current_iPropL fr [("H1", (P -∗ Q)%I); ("A", X); ("H0", P); ("B", Y)]),
      False.
  Proof.
    i. mAssert _ with "- B A" as "H0".
    { iSpecialize ("H1" with "H0"). iExact "H1". }
  Abort.

  (* mAssertPure *)
  Goal forall fr P X Y
              (ACC: current_iPropL fr [("A", X); ("H0", (X -∗ ⌜P⌝)%I); ("B", Y)]),
      False.
  Proof.
    i. mAssertPure P as PURE.
    { iClear "B". iApply "H0". iApply "A". }
  Abort.

  Goal forall fr P X Y
              (ACC: current_iPropL fr [("A", X); ("H0", (X -∗ ⌜P⌝)%I); ("B", Y)]),
      False.
  Proof.
    i. mAssertPure P as PURE.
    { iClear "B". iApply "H0". iApply "A". }
  Abort.

  Goal forall fr P X Y
              (ACC: current_iPropL fr [("A", X); ("H0", (X -∗ ⌜P⌝)%I); ("B", Y)]),
      False.
  Proof.
    i. mAssertPure _ as PURE.
    { iClear "B". iApply "H0". iApply "A". }
  Abort.

  Goal forall fr P X Y
              (ACC: current_iPropL fr [("A", X); ("H0", (X -∗ ⌜P⌝)%I); ("B", Y)]),
      False.
  Proof.
    i. mAssertPure _.
    { iClear "B". iApply "H0". iApply "A". }
  Abort.

  (* mEval *)
  Goal forall fr X Y
              (ACC: current_iPropL fr [("A", X); ("H0", (X -∗ ⌜(6 + 6 = 12)%nat⌝)%I); ("B", Y)]),
      False.
  Proof.
    i. mEval ltac:(simpl) in "H0". (* simpl, rewrite, unfold, and fold ... anything *)
  Abort.

  (* mRename *)
  Goal forall fr P X Y
              (ACC: current_iPropL fr [("A", X); ("H0", (X -∗ ⌜P⌝)%I); ("B", Y)]),
      False.
  Proof.
    i. mRename "H0" into "H".
  Abort.

End TEST.


Module PARSE.
  Section PARSE.
    Context `{Σ: GRA.t}.

    Inductive iProp_tree: Type :=
    | iProp_tree_base (P: iProp)
    | iProp_tree_binop (op: iProp -> iProp -> iProp) (tr0 tr1: iProp_tree)
    | iProp_tree_unop (op: iProp -> iProp) (tr: iProp_tree)
    | iProp_tree_kop A (op: (A -> iProp) -> iProp) (k: A -> iProp_tree)
    .

    Fixpoint from_iProp_tree (tr: iProp_tree): iProp :=
      match tr with
      | iProp_tree_base P => P
      | iProp_tree_binop op P Q => op (from_iProp_tree P) (from_iProp_tree Q)
      | iProp_tree_unop op P => op (from_iProp_tree P)
      | @iProp_tree_kop A op k => op (fun a => from_iProp_tree (k a))
      end.

    Definition holeT: Type := forall A, A.

    (* To use it, declare Variable hole: forall A, A. *)
    Ltac parse_iProp_tree hole p :=
      match p with
      | ?op (?P0: iProp) (?P1: iProp) =>
        let tr0 := parse_iProp_tree hole P0 in
        let tr1 := parse_iProp_tree hole P1 in
        constr:(iProp_tree_binop op tr0 tr1)
      | ?op (?P: iProp) =>
        let tr := parse_iProp_tree hole P in
        constr:(iProp_tree_unop op tr)
      | ?op ?k =>
        match type of k with
        | ?A -> bi_car iProp =>
          let khole := (eval cbn beta in (k (@hole A))) in
          let tr := parse_iProp_tree hole khole in
          let fhole := (eval pattern (@hole A) in tr) in
          match fhole with
          | ?f (@hole A) => constr:(@iProp_tree_kop A op f)
          end
        end
      | ?P => constr:(iProp_tree_base P)
      end.

    (* demo *)
    Variable hole: holeT. (* absurd axiom but will not appear in the final proof *)

    Goal forall (Q0: bool -> iProp) (Q1: iProp) r,
        (∃ (n: nat), (((∀ (b: bool), Q0 b)%I) ∧ Q1) ** #=> ⌜(n = 2 * n - 1)%nat⌝)%I r.
    Proof.
      intros Q0 Q1 r.
      match goal with
      | |- iProp_pred ?P0 r =>
        let P1 := (parse_iProp_tree hole P0) in
        change P0 with (from_iProp_tree P1)
      end.
    Abort.

  End PARSE.
End PARSE.



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
