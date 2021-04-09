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


Let Σ: GRA.t := fun _ => of_RA.t RA.empty.
Local Existing Instance Σ.

Definition main0: itree Es Any.t :=
  n <- trigger (Choose nat) ;;
  r <- trigger (Syscall "print" [Vint (Z.of_nat n)] top1) ;;
  Ret r↑
.

Definition Ex0: Mod.t := {|
  Mod.get_modsem :=
    fun _ => {|
        ModSem.fnsems := [("main", fun _ => main0)];
        ModSem.initial_mrs := [("Main", (ε, unit↑))];
      |};
  Mod.sk := Sk.unit;
                        |}
.

Definition ex0 := ModSem.initial_itr_no_check (Mod.enclose Ex0).
