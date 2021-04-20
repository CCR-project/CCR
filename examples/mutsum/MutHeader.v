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

  Definition main_spec: fspec := mk_simple (fun (_: unit) => ((fun _ o _ => o = ord_top), top2)).
  Definition f_spec:    fspec := mk_simple (fun (n: nat) => ((fun varg o _ => varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n),
                                                             (fun vret _ => vret = (Vint (Z.of_nat (sum n)))↑))).
  Definition g_spec:    fspec := mk_simple (fun (n: nat) => ((fun varg o _ => varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n),
                                                             (fun vret _ => vret = (Vint (Z.of_nat (sum n)))↑))).
  Definition GlobalStb: list (gname * fspec) := [("main", main_spec); ("f", f_spec); ("g", g_spec)].

End PROOF.
