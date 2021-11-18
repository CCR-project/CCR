Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.

Set Implicit Arguments.


Notation mblock := nat (only parsing).
Notation ptrofs := Z (only parsing).


Create HintDb stb.
Hint Rewrite (Seal.sealing_eq "stb"): stb.

Definition to_stb `{Σ: GRA.t} (l: alist gname fspec): gname -> option fspec :=
  fun fn => alist_find fn l.

Definition to_stb_context `{Σ: GRA.t} (stbu: list gname) (stbk: alist gname fspec) :=
  to_stb (List.map (fun fn => (fn, fspec_trivial)) stbu ++ stbk).

Definition to_closed_stb `{Σ: GRA.t} (l: alist gname fspec): gname -> option fspec :=
  fun fn => match alist_find fn l with
            | Some fsp => Some fsp
            | _ => Some fspec_trivial
            end.

Ltac stb_tac :=
  match goal with
  | [ |- to_stb_context _ _ _ = _ ] =>
    unfold to_stb_context, to_stb;
    autounfold with stb; autorewrite with stb; simpl
  | [ |- to_stb ?xs _ = _ ] =>
    unfold to_stb;
    autounfold with stb; autorewrite with stb; simpl
  | [ |- to_closed_stb ?xs _ = _ ] =>
    unfold to_closed_stb;
    autounfold with stb; autorewrite with stb; simpl
  | [ |- alist_find _ ?xs = _ ] =>
    match type of xs with
    | (list (string * fspec)) =>
      autounfold with stb; autorewrite with stb; simpl
    end
  | [H: alist_find _ ?xs = _ |- _ ] =>
    match type of xs with
    | (list (string * fspec)) =>
      autounfold with stb in H; autorewrite with stb in H; simpl in H
    end
  | [H: to_stb_context _ _ _ = _ |- _ ] =>
    unfold to_stb_context, to_stb in H;
    autounfold with stb in H; autorewrite with stb in H; simpl in H
  | [H: to_stb ?xs _ = _ |- _ ] =>
    unfold to_stb in H;
    autounfold with stb in H; autorewrite with stb in H; simpl in H
  | [H: to_closed_stb ?xs _ = _ |- _ ] =>
    unfold to_closed_stb in H;
    autounfold with stb in H; autorewrite with stb in H; simpl in H
  end.



Definition ord_weaker (next cur: ord): Prop :=
  match next, cur with
  | ord_pure next, ord_pure cur => (next <= cur)%ord
  (* | _, ord_top => True *)
  | ord_top, ord_top => True
  | _, _ => False
  end
.

Global Program Instance ord_weaker_PreOrder: PreOrder ord_weaker.
Next Obligation.
  ii. destruct x; ss. refl.
Qed.
Next Obligation.
  ii. destruct x, y, z; ss. etrans; et.
Qed.



Section HEADER.

  Context `{Σ: GRA.t}.

  Definition fspec_weaker (fsp_src fsp_tgt: fspec): Prop :=
    forall x_src mn,
    exists x_tgt,
      (<<MEASURE: ord_weaker (fsp_tgt.(measure) x_tgt) (fsp_src.(measure) x_src)>>) ∧
      (<<PRE: forall arg_src arg_tgt,
          (fsp_src.(precond) mn x_src arg_src arg_tgt) ⊢ #=> (fsp_tgt.(precond) mn x_tgt arg_src arg_tgt)>>) ∧
      (<<POST: forall ret_src ret_tgt,
          (fsp_tgt.(postcond) mn x_tgt ret_src ret_tgt) ⊢ #=> (fsp_src.(postcond) mn x_src ret_src ret_tgt)>>)
  .

  Global Program Instance fspec_weaker_PreOrder: PreOrder fspec_weaker.
  Next Obligation.
  Proof.
    ii. exists x_src. esplits; ii.
    { refl. }
    { iStartProof. iIntros "H". iApply "H". }
    { iStartProof. iIntros "H". iApply "H". }
  Qed.
  Next Obligation.
  Proof.
    ii. hexploit (H x_src). i. des.
    hexploit (H0 x_tgt). i. des. esplits; ii.
    { etrans; et. }
    { iStartProof. iIntros "H".
      iApply bupd_idemp. iApply PRE0.
      iApply bupd_idemp. iApply PRE. iApply "H". }
    { iStartProof. iIntros "H".
      iApply bupd_idemp. iApply POST.
      iApply bupd_idemp. iApply POST0. iApply "H". }
  Qed.

  Variant fn_has_spec (stb: gname -> option fspec) (fn: gname) (fsp: fspec): Prop :=
  | fn_has_spec_intro
      fsp1
      (FIND: stb fn = Some fsp1)
      (WEAK: fspec_weaker fsp fsp1)
  .
  Hint Constructors fn_has_spec: core.

  Lemma fn_has_spec_weaker (stb: gname -> option fspec) (fn: gname) (fsp0 fsp1: fspec)
        (SPEC: fn_has_spec stb fn fsp1)
        (WEAK: fspec_weaker fsp0 fsp1)
    :
      fn_has_spec stb fn fsp0.
  Proof.
    inv SPEC. econs; eauto. etrans; eauto.
  Qed.

  Definition stb_incl (stb0 stb1: gname -> option fspec): Prop :=
    forall fn fsp (FIND: stb0 fn = Some fsp), stb1 fn = Some fsp.

  Global Program Instance stb_incl_PreOrder: PreOrder stb_incl.
  Next Obligation.
  Proof.
    ii. ss.
  Qed.
  Next Obligation.
  Proof.
    ii. eapply H0, H, FIND.
  Qed.

  Lemma incl_to_stb stb0 stb1 (INCL: List.incl stb0 stb1)
        (NODUP: NoDup (List.map fst stb1))
    :
      stb_incl (to_stb stb0) (to_stb stb1).
  Proof.
    unfold to_stb. ii.
    eapply alist_find_some in FIND. eapply INCL in FIND.
    eapply alist_find_some_iff in FIND; et.
  Qed.

  Lemma to_stb_context_incl stbu stbk stball
        (INCL: List.incl stbk stball)
        (NODUP: NoDup (stbu ++ (List.map fst stball)))
    :
      stb_incl (to_stb_context stbu stbk) (to_closed_stb stball).
  Proof.
    unfold to_stb_context, to_stb, to_closed_stb. ii.
    rewrite alist_find_app_o in FIND.
    destruct (alist_find fn (map (fun fn => (fn, fspec_trivial)) stbu)) eqn:EQ; clarify.
    { eapply alist_find_some in EQ. eapply in_map_iff in EQ. des. clarify.
      des_ifs. exfalso. eapply alist_find_some in Heq.
      eapply NoDup_app_disjoint in NODUP; et.
      eapply in_map with (f:=fst) in Heq. ss. }
    { eapply alist_find_some in FIND. eapply INCL in FIND.
      eapply alist_find_some_iff in FIND; et.
      rewrite FIND; et. eapply nodup_app_r; et. }
  Qed.

  Definition stb_weaker (stb0 stb1: gname -> option fspec): Prop :=
    forall fn fsp0 (FINDTGT: stb0 fn = Some fsp0),
    exists fsp1,
      (<<FINDSRC: stb1 fn = Some fsp1>>) /\
      (<<WEAKER: fspec_weaker fsp0 fsp1>>)
  .

  Global Program Instance stb_weaker_PreOrder: PreOrder stb_weaker.
  Next Obligation. ii. esplits; eauto. refl. Qed.
  Next Obligation.
    ii. r in H. r in H0. exploit H; et. intro T; des.
    exploit H0; et. intro U; des. esplits; eauto. etrans; et.
  Qed.

  Lemma stb_incl_weaker: stb_incl <2= stb_weaker.
  Proof.
    ii. eapply PR in FINDTGT. esplits; et. refl.
  Qed.

  Lemma incl_stb_incl: forall stb0 stb1 (NODUP: List.NoDup (List.map fst stb1)) (INCL: incl stb0 stb1), stb_incl (to_stb stb0) (to_stb stb1).
  Proof.
    unfold to_stb.
    ii. eapply alist_find_some in FIND.
    destruct (alist_find fn stb1) eqn:T.
    { eapply alist_find_some in T.
      eapply INCL in FIND.
      destruct (classic (fsp = f)).
      { subst. esplits; et. }
      exfalso.
      eapply NoDup_inj_aux in NODUP; revgoals.
      { eapply T. }
      { eapply FIND. }
      { ii; clarify. }
      ss.
    }
    eapply alist_find_none in T; et. exfalso. et.
  Qed.

  Lemma incl_weaker: forall stb0 stb1 (NODUP: List.NoDup (List.map fst stb1)) (INCL: incl stb0 stb1), stb_weaker (to_stb stb0) (to_stb stb1).
  Proof.
    i. eapply stb_incl_weaker. eapply incl_stb_incl; et.
  Qed.

  Lemma app_incl: forall stb0 stb1, stb_incl (to_stb stb0) (to_stb (stb0 ++ stb1)).
  Proof.
    unfold to_stb.
    ii. eapply alist_find_app in FIND. esplits; eauto.
  Qed.

  Lemma app_weaker: forall stb0 stb1, stb_weaker (to_stb stb0) (to_stb (stb0 ++ stb1)).
  Proof.
    i. eapply stb_incl_weaker. eapply app_incl.
  Qed.

  Lemma to_closed_stb_weaker stb
    :
      stb_incl (to_stb stb) (to_closed_stb stb).
  Proof.
    unfold to_closed_stb, to_stb. ii. rewrite FIND. auto.
  Qed.

  Lemma incl_to_closed_stb stb0 stb1 (INCL: List.incl stb0 stb1)
        (NODUP: NoDup (List.map fst stb1))
    :
      stb_incl (to_stb stb0) (to_closed_stb stb1).
  Proof.
    unfold to_stb, to_closed_stb. ii.
    eapply alist_find_some in FIND. eapply INCL in FIND.
    eapply alist_find_some_iff in FIND; et.
    rewrite FIND. et.
  Qed.

  Variable skenv: SkEnv.t.

  Variant fb_has_spec (stb: gname -> option fspec) (fb: mblock) (fsp: fspec): Prop :=
  | fb_has_spec_intro
      fn
      (FBLOCK: skenv.(SkEnv.blk2id) fb = Some fn)
      (SPEC: fn_has_spec stb fn fsp)
  .

  Lemma fb_has_spec_weaker (stb: gname -> option fspec) (fb: mblock) (fsp0 fsp1: fspec)
        (SPEC: fb_has_spec stb fb fsp1)
        (WEAK: fspec_weaker fsp0 fsp1)
    :
      fb_has_spec stb fb fsp0.
  Proof.
    inv SPEC. econs; eauto.
    eapply fn_has_spec_weaker; eauto.
  Qed.

End HEADER.


Ltac stb_incl_tac :=
  i; eapply incl_to_stb;
  [ autounfold with stb; autorewrite with stb; ii; ss; des; clarify; auto|
    autounfold with stb; autorewrite with stb; repeat econs; ii; ss; des; ss].

Ltac stb_context_incl_tac :=
  i; eapply to_stb_context_incl;
  [ autounfold with stb; autorewrite with stb; ii; ss; des; clarify; auto|
    autounfold with stb; autorewrite with stb; repeat econs; ii; ss; des; ss].

Ltac ors_tac := repeat ((try by (ss; left; ss)); right).
