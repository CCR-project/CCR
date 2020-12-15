Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.


Fixpoint sum (n: nat): nat :=
  match n with
  | O => O
  | S m => n + sum m
  end
.
Compute (sum 10).

Section PROOF.

  Context `{Σ: GRA.t}.

  Definition GlobalStb: list (fname * fspec) := [
    ("main", mk "F" (X:=unit) top3 top3) ;
    ("f", mk "F" (X:=nat) (fun n varg _ => varg = [Vint (Z.of_nat n)]) (fun n vret _ => vret = Vint (Z.of_nat (sum n)))) ;
    ("g", mk "F" (X:=nat) (fun n varg _ => varg = [Vint (Z.of_nat n)]) (fun n vret _ => vret = Vint (Z.of_nat (sum n))))
  ].

End PROOF.
