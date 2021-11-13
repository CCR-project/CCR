Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.

Set Implicit Arguments.


Definition knotRA: URA.t := Auth.t (Excl.t (option (nat -> nat))).
Definition knot_full (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.black (M:=(Excl.t _)) (Some f).
Definition knot_frag (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.white (M:=(Excl.t _)) (Some f).

Definition knot_init: (@URA.car knotRA) := knot_frag None.

Section REC.
  Context `{Σ: GRA.t}.

  Definition mrec_spec (f: nat -> nat) (INV: iProp): fspec :=
    mk_simple (X:=nat)
              (fun n => (
                   (ord_pure (2 * n + 1)%nat),
                   (fun varg =>
                      (⌜varg = [Vint (Z.of_nat n)]↑ /\ (intrange_64 n)⌝)
                        ** INV
                   ),
                   (fun vret =>
                      (⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                        ** INV
                   )
              )).

End REC.
