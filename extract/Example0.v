Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.

Set Implicit Arguments.


Let Σ: GRA.t := fun _ => of_RA.t RA.empty.
Local Existing Instance Σ.

Definition main0: itree EventsL.Es Any.t :=
  n <- trigger (Choose nat) ;;
  r <- trigger (Syscall "print" [(Z.of_nat n)]↑ top1) ;;
  Ret r
.

Definition Ex0: ModL.t := {|
  ModL.get_modsem :=
    fun _ => {|
        ModSemL.fnsems := [("main", fun _ => main0)];
        ModSemL.initial_mrs := [("Main", unit↑)];
      |};
  ModL.sk := Sk.unit;
                        |}
.

Definition ex0 := ModSemL.initial_itr (ModL.enclose Ex0) None.
