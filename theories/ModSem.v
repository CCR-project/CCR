Require Import sflib.
Require Import Universe.
Require Import Sem.
Require Import Behavior.
From Paco Require Import paco.
Require Import RelationClasses List.
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.
Require Import String.

Set Implicit Arguments.

Module ModSem.

  Inductive sort: Type :=
  | angelic
  | demonic
  | final (retv: val)
  | vis
  | at_external (args: list val)
  .

  Record t: Type := mk {
    state: Type;
    local_data: Type;
    step (st0: state) (ev: option event) (st1: state): Prop;
    state_sort: state -> sort;
  }
  .

End ModSem.
