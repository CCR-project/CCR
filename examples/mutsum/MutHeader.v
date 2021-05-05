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
Require Import Logic.

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

  Definition main_spec: fspec := mk_simple (fun (_: unit) => ((fun _ o => (⌜o = ord_top⌝: iProp)%I), fun _ => (True: iProp)%I)).
  Definition f_spec:    fspec := mk_simple (fun (n: nat) => ((fun varg o => (⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n⌝: iProp)%I),
                                                             (fun vret => (⌜vret = (Vint (Z.of_nat (sum n)))↑⌝: iProp)%I))).
  Definition g_spec:    fspec := mk_simple (fun (n: nat) => ((fun varg o => (⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n⌝: iProp)%I),
                                                             (fun vret => (⌜vret = (Vint (Z.of_nat (sum n)))↑⌝: iProp)%I))).
  Definition GlobalStb: list (gname * fspec) := [("main", main_spec); ("f", f_spec); ("g", g_spec)].

End PROOF.
