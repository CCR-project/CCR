Require Import Coqlib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import IPM.
Require Import SimModSem.
Require Import STB.

Set Implicit Arguments.







Section AUX.
  Definition invRA: URA.t := Excl.t unit.

  Definition inv_token: (@URA.car invRA) := Some tt.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.

  Definition inv_closed: iProp := OwnM inv_token%I.

  Lemma inv_closed_unique
    :
      inv_closed -∗ inv_closed -∗ False
  .
  Proof.
    unfold inv_closed, inv_token.
    iIntros "H0 H1".
    iCombine "H0 H1" as "H". iOwnWf "H" as WF. exfalso.
    repeat ur in WF. ss.
  Qed.

  Definition inv_le
             A (le: A -> A -> Prop)
    :
      (A + Any.t * Any.t) -> (A + Any.t * Any.t) -> Prop :=
    fun x0 x1 =>
      match x0, x1 with
      | inl a0, inl a1 => le a0 a1
      | inr st0, inr st1 => st0 = st1
      | _, _ => False
      end.

  Lemma inv_le_PreOrder A (le: A -> A -> Prop)
        (PREORDER: PreOrder le)
    :
      PreOrder (inv_le le).
  Proof.
    econs.
    { ii. destruct x; ss. refl. }
    { ii. destruct x, y, z; ss.
      { etrans; et. }
      { subst. auto. }
    }
  Qed.

  Definition mk_fspec_inv (fsp: fspec): fspec :=
    @mk_fspec
      _
      (meta fsp)
      fsp.(measure)
      (fun mn x varg_src varg_tgt =>
         inv_closed ** (precond fsp) mn x varg_src varg_tgt)
      (fun mn x vret_src vret_tgt =>
         inv_closed ** (postcond fsp) mn x vret_src vret_tgt).

  Lemma fspec_weaker_fspec_inv_weakker (fsp0 fsp1: fspec)
        (WEAKER: fspec_weaker fsp0 fsp1)
    :
      fspec_weaker (mk_fspec_inv fsp0) (mk_fspec_inv fsp1).
  Proof.
    ii. exploit WEAKER. i. des. exists x_tgt. esplits; ss; et.
    { ii. iIntros "[INV H]". iSplitL "INV"; ss.
      iApply PRE. iExact "H". }
    { ii. iIntros "[INV H]". iSplitL "INV"; ss.
      iApply POST. iExact "H". }
  Qed.

End AUX.
