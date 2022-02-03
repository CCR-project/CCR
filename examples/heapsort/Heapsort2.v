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

  Definition create_body : list Z * nat -> itree hEs (list Z) :=
    fun _ => trigger (Choose _).

  Definition create_spec : fspec :=
    mk_simple (X := list Z * nat)
              (fun '(base, i) =>
                 (ord_top,
                  fun varg => ⌜varg = (base, i)↑⌝,
                  fun vret => ∃ base' : list Z, ⌜vret = base'↑ /\ Permutation base base'⌝
                 )                           
              )%I.
  
  Definition heapify_body : (list Z * Z) -> itree hEs (list Z) :=
    fun _ => trigger (Choose _).

  Definition heapify_spec : fspec :=
    mk_simple (X := list Z * Z)
              (fun '(base, k) =>
                ( ord_top
                , fun varg => ⌜varg = (base, k)↑⌝
                , fun vret => ∃ base' : list Z, ⌜vret = base'↑ /\ Permutation (k :: tail base) base'⌝
                )
              )%I.

  Definition heapsort_body : list Z -> itree hEs (list Z) :=
    fun xs =>
      ys <- trigger (Choose (list Z));;
      Ret ys.

  Definition heapsort_spec : fspec :=
    mk_simple (X := list Z)
              (fun xs => (
                   ord_top,
                   (fun varg => ⌜varg = xs↑⌝),
                   (fun vret => ∃ ys : list Z, ⌜vret = ys↑ /\ Permutation xs ys /\ Sorted Z.le ys⌝)
                 )
              )%I.

  Definition HeapsortSbtb : list (gname * fspecbody) :=
    [("create",  mk_specbody create_spec   (cfunN create_body));
    ("heapify",  mk_specbody heapify_spec  (cfunN heapify_body));
    ("heapsort", mk_specbody heapsort_spec (cfunN heapsort_body))
    ].

  Definition SHeapsortSem : SModSem.t := {|
    SModSem.fnsems := HeapsortSbtb;
    SModSem.mn := "Heapsort";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}.

  Definition SHeapsort : SMod.t := {|
    SMod.get_modsem := fun _ => SHeapsortSem;
    SMod.sk := Sk.unit;
  |}.

  Definition Heapsort stb : Mod.t := (SMod.to_tgt stb) SHeapsort.

End HEAPSORT.
