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



Section PROOF.

  Context `{Σ: GRA.t}.
  (* Context `{@GRA.inG memRA Σ}. *)

  (***
        void* x = malloc(1);
        *x = 42;
        unknown_call(x);
        y = *x;
        return y;
   ***)
  Definition mainF: list val -> itree Es val :=
    fun _ =>
      x <- trigger (Call "alloc" [Vint 1]);;
      trigger (Call "store" [x ; Vint 42]);;
      trigger (Call "unknown_call" [x]);;
      y <- trigger (Call "load" [x]);;
      Ret y
  .

  Definition MainSem: ModSem.t := {|
    ModSem.fnsems := [("main", mainF)];
    ModSem.initial_mrs := [("Main", ε)];
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
