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


Section HEADER.

  Context `{Σ: GRA.t}.

  Definition fspec_weaker (fsp_src fsp_tgt: fspec): Prop :=
    forall x_src mn,
    exists x_tgt,
      (<<PRE: forall arg_src arg_tgt o,
          (fsp_src.(precond) mn x_src arg_src arg_tgt o) ⊢ #=> (fsp_tgt.(precond) mn x_tgt arg_src arg_tgt o)>>) /\
      (<<POST: forall ret_src ret_tgt,
          (fsp_tgt.(postcond) mn x_tgt ret_src ret_tgt) ⊢ #=> (fsp_src.(postcond) mn x_src ret_src ret_tgt)>>)
  .

  Global Program Instance fspec_weaker_PreOrder: PreOrder fspec_weaker.
  Next Obligation.
  Proof.
    ii. exists x_src. esplits; ii.
    { iStartProof. iIntros "H". iApply "H". }
    { iStartProof. iIntros "H". iApply "H". }
  Qed.
  Next Obligation.
  Proof.
    ii. hexploit (H x_src). i. des.
    hexploit (H0 x_tgt). i. des. esplits; ii.
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
