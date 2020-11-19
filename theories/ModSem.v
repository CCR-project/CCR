From Paco Require Import paco.
Require Import Program.
Require Import sflib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import Skeleton.

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
    step (skenv: SkEnv.t) (st0: state) (ev: option event) (st1: state): Prop;
    state_sort: state -> sort;
    initial_local_data: local_data;
    sk: Sk.t;
    name: string;
  }
  .

End ModSem.
