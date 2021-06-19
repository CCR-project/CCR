Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import Mem1.
Require Import TODOYJ.

Set Implicit Arguments.

(*** TODO: move to Universe ***)
Global Program Instance val_dec: Dec val.
Next Obligation.
  repeat (decide equality).
Defined.

Definition INT_MIN: Z := - 1.
