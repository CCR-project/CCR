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
Require Import Coq.Sorting.Sorted.

Set Implicit Arguments.

Section HEAPSORT.

  Context `{Σ : GRA.t}.

  Definition create_body : list Z * nat -> itree Es (list Z) :=
    fun _ => trigger (Choose _).

  Definition create_spec : fspec :=
    mk_simple (X := list Z * nat)
              (fun '(base, i) =>
                 (ord_top,
                  fun varg => ⌜varg = (base, i)↑⌝,
                  fun vret => ∃ base' : list Z, ⌜vret = base'↑ /\ Permutation base base'⌝
                 )                           
              )%I.
  
  Definition heapify_body : (list Z * Z) -> itree Es (list Z) :=
    fun _ => trigger (Choose _).

  Definition heapify_spec : fspec :=
    mk_simple (X := list Z * Z)
              (fun '(base, k) =>
                ( ord_top
                , fun varg => ⌜varg = (base, k)↑⌝
                , fun vret => ∃ base' : list Z, ⌜vret = base'↑ /\ Permutation (k :: tail base) base'⌝
                )
              )%I.

  Definition sort_body : list Z -> itree Es (list Z) :=
    fun xs =>
      ys <- trigger (Choose (list Z));;
      Ret ys.

  Definition sort_spec : fspec :=
    mk_simple (X := list Z)
              (fun xs => (
                   ord_top,
                   (fun varg => ⌜varg = xs↑⌝),
                   (fun vret => ∃ ys : list Z, ⌜vret = ys↑ /\ Permutation xs ys /\ Sorted Z.le ys⌝)
                 )
              )%I.

End HEAPSORT.
