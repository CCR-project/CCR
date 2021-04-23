Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.


Section HEADER.

  Context `{Σ: GRA.t}.



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
