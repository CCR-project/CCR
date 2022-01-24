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

Set Implicit Arguments.

Section HEAPSORT.
  Context `{Σ : GRA.t}.
         
  Definition create_body : list val -> itree hEs val.
  Admitted.

  Definition create_spec : fspec.
  Admitted.

  Definition heapify_body : list val -> itree hEs val.
  Admitted.

  Definition heapify_spec : fspec.
  Admitted.
  
  Definition heapsort_body : list val -> itree hEs val.
  Admitted.

  Definition heapsort_spec : fspec.
  Admitted.
  
  Definition HeapsortSbtb : list (gname * fspecbody) :=
    [("create", mk_specbody create_spec (cfunN create_body));
    ("heapify", mk_specbody heapify_spec (cfunN heapify_body));
    ("heapsort", mk_specbody heapsort_spec (cfunN heapsort_spec));
    ].

  Definition SHeapsortSem : SModSem.t.
  Admitted.

  Definition SHeapsort : SMod.t.
  Admitted.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Heapsort : Mod.t := SMod.to_tgt GlobalStb SHeapsort.
End HEAPSORT.
