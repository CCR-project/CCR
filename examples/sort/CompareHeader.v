Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import MutHeader.
Require Import Logic.

Set Implicit Arguments.


(* TODO: move it to better place *)
Definition Vbool (b: bool): val :=
  if b then Vint 0 else Vint 1.

Definition mycmp (n0 n1: Z): Z :=
  if (Z_le_gt_dec n0 n1)
  then 0
  else 1.

Definition compare_gen `{Σ: GRA.t} (f: Z -> Z -> Z) (mn: mname): fspec :=
  mk_simple mn (X:=Z*Z)
            (fun '(n0, n1) => (
                 (fun varg o => ⌜varg = [Vint n0; Vint n1]↑ /\ o = ord_pure 0⌝),
                 (fun vret => ⌜vret = (Vint (f n0 n1))↑⌝)
            )).
