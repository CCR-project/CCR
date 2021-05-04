Require Export IPM.

Require Import Coqlib.
Require Import Universe.
Require Import PCM.

Set Implicit Arguments.
Set Typeclasses Depth 5.



Infix "**" := bi_sep (at level 99).
Infix "-*" := bi_wand (at level 99, right associativity).
Notation "|=> P" := (bupd P) (at level 99).




Section IRIS.
  Context {Σ: GRA.t}.

  Lemma Own_extends
        (a b: Σ)
        (EXT: URA.extends a b)
    :
      Own b ⊢ Own a
  .
  Proof.
    red. uipropall. ii. etrans; et.
  Qed.

  Lemma own_sep'
        (r0 r1 r2: Σ)
        (ADD: r0 = r1 ⋅ r2)
    :
      Own r0 = Sepconj (Own r1) (Own r2)
  .
  Proof.
    uipropall.
    apply func_ext. i. apply prop_ext.
    split; ii.
    - clarify. des. r in H. des. exists r1, (r2 ⋅ ctx). esplits; et.
      + rewrite URA.add_assoc. ss.
      + refl.
      + rr. esplits; et.
    - des. clarify. r in H0. r in H1. etrans.
      { eapply URA.extends_add; et. }
      rewrite ! (URA.add_comm a).
      eapply URA.extends_add; et.
  Qed.

  Lemma own_sep
        (r1 r2: Σ)
    :
      Own (r1 ⋅ r2) ⊣⊢ (Own r1 ** Own r2)
  .
  Proof.
    erewrite <- own_sep'; et.
  Qed.

  Lemma own_upd2_set
        (r1: Σ) B
        (UPD: URA.updatable_set r1 B)
    :
      (Own r1) ⊢ (bupd (∃ b, ⌜B b⌝ ** (Own b)))
  .
  Proof.
    cut (Entails (Own r1) (Upd (Ex (fun b => Sepconj (Pure (B b)) (Own b))))); ss.
    uipropall. i. red in H. des. subst.
    exploit (UPD (ctx0 ⋅ ctx)).
    { rewrite URA.add_assoc. et. }
    i. des. exists (b ⋅ ctx0). split.
    { rewrite <- URA.add_assoc. et. }
    { exists b. uipropall. esplits; [|apply IN|refl].
      eapply URA.add_comm. }
  Qed.

  Lemma own_upd
        (r1 r2: Σ)
        (UPD: URA.updatable r1 r2)
    :
      (Own r1) ⊢ (bupd (Own r2))
  .
  Proof.
    iStartProof. iIntros "H".
    iAssert (bupd (∃ b, bi_pure ((eq r2) b) ** (Own b)))%I with "[H]" as "H".
    { iApply own_upd2_set; [|iFrame].
      red. red in UPD. i. hexploit UPD; et. }
    iMod "H". iDestruct "H" as (b) "[#H0 H1]".
    iPure "H0" as Hs. subst. iApply "H1".
  Qed.

End IRIS.
