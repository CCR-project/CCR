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
