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



Definition knotRA: URA.t := Auth.t (Excl.t (option (nat -> nat))).
Definition knot_full (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.black (M:=(Excl.t _)) (Some f).
Definition knot_frag (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.white (M:=(Excl.t _)) (Some f).

Definition knot_init: (@URA.car knotRA) := knot_frag None.

Section REC.

  Context `{Σ: GRA.t}.

  Definition mrec_spec (f: nat -> nat) (INV: Σ -> Prop): ftspec (list val) val :=
    mk_simple (X:=nat)
              (fun n => (
                   (fun varg o =>
                      (⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n + 1)⌝)
                        ** INV),
                   (fun vret =>
                      (⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                        ** INV)
              )).

End REC.
