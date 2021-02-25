Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import SimModSem.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.


Fixpoint sum (n: nat): nat :=
  match n with
  | O => O
  | S m => n + sum m
  end
.
Compute (sum 10). (* 55 *)





Section PROOF.

  Context `{Σ: GRA.t}.

  Definition main_spec: fspec := mk_simple "Main" (X:=unit) (fun _ _ o _ => o = ord_top) top3.
  Definition f_spec:    fspec := mk_simple "F" (X:=nat) (fun n varg o _ => varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n) (fun n vret _ => vret = (Vint (Z.of_nat (sum n)))↑).
  Definition g_spec:    fspec := mk_simple "G" (X:=nat) (fun n varg o _ => varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n) (fun n vret _ => vret = (Vint (Z.of_nat (sum n)))↑).
  Definition GlobalStb: list (gname * fspec) := [("main", main_spec); ("f", f_spec); ("g", g_spec)].

End PROOF.
