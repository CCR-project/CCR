Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic YPM.

Set Implicit Arguments.






Definition invRA: URA.t := Auth.t (Excl.t unit).
Definition inv_black : (@URA.car invRA) := Auth.black (M:=(Excl.t unit)) (Some tt).
Definition inv_white : (@URA.car invRA) := Auth.white (M:=(Excl.t unit)) (Some tt).

Section AUX.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.

  Definition inv_open: iProp := OwnM inv_black.
  Definition inv_closed: iProp := OwnM inv_white.

  Lemma inv_closed_unique
    :
      inv_closed -∗ inv_closed -∗ False
  .
  Proof.
    iIntros "H0 H1".
    unfold inv_closed, inv_white in *.
    iCombine "H0 H1" as "H". iOwnWf "H". iPureIntro.
    repeat ur in H0. ss.
  Qed.

  Lemma inv_open_unique
    :
      inv_open -∗ inv_open -∗ False
  .
  Proof.
    iIntros "H0 H1".
    unfold inv_open, inv_black in *.
    iCombine "H0 H1" as "H". iOwnWf "H". iPureIntro.
    repeat ur in H0. ss.
  Qed.
End AUX.


Definition knotRA: URA.t := Auth.t (Excl.t (option (nat -> nat))).
Definition knot_full (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.black (M:=(Excl.t _)) (Some f).
Definition knot_frag (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.white (M:=(Excl.t _)) (Some f).

Definition knot_init: (@URA.car knotRA) := knot_frag None.

Section REC.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.

  Definition mrec_spec (f: nat -> nat) (INV: iProp): ftspec (list val) val :=
    mk_simple (X:=nat)
              (fun n => (
                   (fun varg o =>
                      (⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n + 1)%nat⌝)
                        ** INV
                   ),
                   (fun vret =>
                      (⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                        ** INV
                   )
              )).

End REC.
