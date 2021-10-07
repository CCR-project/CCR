Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import ProofMode.

Set Implicit Arguments.


Definition max: nat := 1000%nat.

Section PROOF.

  Context `{Σ: GRA.t}.

  Definition f_spec: fspec :=
    mk_simple (fun (n: nat) =>
                 ((fun varg o => (⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n /\ n < max⌝: iProp)%I),
                  (fun vret => (⌜vret = (Vint (Z.of_nat (5 * n)))↑⌝: iProp)%I))).
  Definition g_spec: fspec :=
    mk_simple (fun (n: nat) =>
                 ((fun varg o => (⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n /\ n < max⌝: iProp)%I),
                  (fun vret => (⌜vret = (Vint (Z.of_nat (5 * n - 2)))↑⌝: iProp)%I))).
  Definition GlobalStb: gname -> option fspec := to_stb [("f", f_spec); ("g", g_spec)].

End PROOF.
