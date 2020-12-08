Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Require Import Mem1.



Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Definition mainF: list val -> itree Es val :=
    fun _ =>
      (* sz <- trigger (Choose _);; *)
      let sz: nat := 1%nat in
      varg <- trigger (Choose _);;
      guarantee(varg = [Vint (Z.of_nat sz)]);;
      (HoareCall "main" top1
                 (fun vret rret => exists b, vret = Vptr b 0 /\
                      rret = GRA.padding
                               (fold_left URA.add (mapi (fun n _ => (b, Z.of_nat n) |-> (Vint 0))
                                                        (List.repeat tt sz)) URA.unit))
                 "alloc" varg);;
      triggerUB
      (* trigger (Call "alloc" [Vint (Z.of_nat 1)]);; *)
      (* trigger (Call "load"  *)
  .

End PROOF.
