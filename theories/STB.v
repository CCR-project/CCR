Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Logic.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.


Section HEADER.

  Context `{Σ: GRA.t}.

  Definition ftspec_weaker Y Z (fsp_src fsp_tgt: ftspec Y Z): Prop :=
    forall (x_src: fsp_src.(X)),
    exists (x_tgt: fsp_tgt.(X)),
      (<<PRE: forall arg_src arg_tgt o,
          (fsp_src.(precond) x_src arg_src arg_tgt o -* fsp_tgt.(precond) x_tgt arg_src arg_tgt o) ε>>) /\
      (<<POST: forall ret_src ret_tgt,
          (fsp_tgt.(postcond) x_tgt ret_src ret_tgt -* fsp_src.(postcond) x_src ret_src ret_tgt) ε>>)
  .

  Global Program Instance ftspec_weaker_PreOrder Y Z: PreOrder (@ftspec_weaker Y Z).
  Next Obligation.
  Proof.
    ii. exists x_src. esplits; ii.
    { rewrite URA.unit_idl. auto. }
    { rewrite URA.unit_idl. auto. }
  Qed.
  Next Obligation.
  Proof.
    ii. hexploit (H x_src). i. des.
    hexploit (H0 x_tgt). i. des. esplits; ii.
    { eapply PRE0; ss. rewrite <- URA.unit_idl. eapply PRE; auto. }
    { eapply POST; ss. rewrite <- URA.unit_idl. eapply POST0; auto. }
  Qed.

  Variant fspec_weaker (fsp_src fsp_tgt: fspec): Prop :=
  | fspec_weaker_intro
      Y Z ftsp_src ftsp_tgt
      (FSPEC0: fsp_src = @mk_fspec _ Y Z ftsp_src)
      (FSPEC1: fsp_tgt = @mk_fspec _ Y Z ftsp_tgt)
      (WEAK: ftspec_weaker ftsp_src ftsp_tgt)
  .

  Global Program Instance fspec_weaker_PreOrder: PreOrder fspec_weaker.
  Next Obligation.
  Proof.
    ii. destruct x. econs; eauto. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0. dependent destruction FSPEC0.
    econs; eauto. etrans; eauto.
  Qed.

  Variant fn_has_spec (stb: list (gname * fspec)) (fn: gname) Y Z (ftsp: ftspec Y Z): Prop :=
  | fn_has_spec_intro
      ftsp1
      (FIND: alist_find fn stb = Some (mk_fspec ftsp1))
      (WEAL: ftspec_weaker ftsp ftsp1)
  .
  Hint Constructors fn_has_spec: core.

  Lemma fn_has_spec_weaker (stb: list (gname * fspec)) (fn: gname) Y Z (ftsp0 ftsp1: ftspec Y Z)
        (SPEC: fn_has_spec stb fn ftsp1)
        (WEAK: ftspec_weaker ftsp0 ftsp1)
    :
      fn_has_spec stb fn ftsp0.
  Proof.
    inv SPEC. econs; eauto. etrans; eauto.
  Qed.

  Definition stb_incl (stb0 stb1: list (gname * fspec)): Prop :=
    forall fn fsp (FIND: alist_find fn stb0 = Some fsp), alist_find fn stb1 = Some fsp.

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

  Variant fb_has_spec (stb: list (gname * fspec)) (fb: block) Y Z (ftsp: ftspec Y Z): Prop :=
  | fb_has_spec_intro
      fn
      (FBLOCK: skenv.(SkEnv.blk2id) fb = Some fn)
      (SPEC: fn_has_spec stb fn ftsp)
  .

  Lemma fb_has_spec_weaker (stb: list (gname * fspec)) (fb: block) Y Z (ftsp0 ftsp1: ftspec Y Z)
        (SPEC: fb_has_spec stb fb ftsp1)
        (WEAK: ftspec_weaker ftsp0 ftsp1)
    :
      fb_has_spec stb fb ftsp0.
  Proof.
    inv SPEC. econs; eauto.
    eapply fn_has_spec_weaker; eauto.
  Qed.

End HEADER.
