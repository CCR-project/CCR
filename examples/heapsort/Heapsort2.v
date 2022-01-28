Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import HeapsortHeader.
Require Import Coq.Sorting.Permutation.

Set Implicit Arguments.

Section HEAPSORT.

  Context `{Σ : GRA.t}.

  Definition sort_body : list Z -> itree Es (list Z) :=
    fun xs =>
      ys <- trigger (Choose (list Z));;
      Ret ys.

  Definition sort_spec : fspec :=
    mk_simple (X := list Z)
              (fun xs => (
                   ord_top,
                   (fun varg => ⌜varg = xs↑⌝),
                   (fun vret => (∃ (ys : list Z), ⌜vret = ys↑ /\ Permutation xs ys⌝))
                 )
              )%I.

End HEAPSORT.
