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
Require Import heapsort.
Require Import ConvC2ITree.

Definition globenv := Clight.globalenv prog.
Definition create_body : list Values.val -> itree Es Values.val  := decomp_func globenv f_create.
Definition heapify_body : list Values.val -> itree Es Values.val := decomp_func globenv f_heapify.
Definition heapsort_body : list Values.val -> itree Es Values.val  := decomp_func globenv f_heapsort.

Definition HeapsortSbtb :=
  [("create",  cfunU create_body);
   ("heapify",  cfunU heapify_body);
   ("heapsort", cfunU heapsort_body)
  ].

Definition HeapsortSem : ModSem.t :=
  {|
    ModSem.fnsems := HeapsortSbtb;
    ModSem.mn := "Heapsort";
    ModSem.initial_st := tt↑;
  |}.

Definition Heapsort : Mod.t :=
  {|
    Mod.get_modsem := fun _ => HeapsortSem;
    Mod.sk := Sk.unit;
  |}.

