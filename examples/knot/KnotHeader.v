Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Definition knotRA: URA.t := Auth.t (Excl.t (option (nat -> nat))).
Definition knot_full (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.black (M:=(Excl.t _)) (Some f).
Definition knot_frag (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.white (M:=(Excl.t _)) (Some f).
