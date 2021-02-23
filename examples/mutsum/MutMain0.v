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

  (***
    main() := return f(10)
  ***)
  Definition mainF: Any.t -> itree Es Any.t :=
    fun varg =>
      r <- trigger (Call "f" [Vint 10]↑);;
      Ret r.

  Definition mainSem: ModSem.t := {|
    ModSem.fnsems := [("main", mainF)];
    ModSem.initial_mrs := [("Main", (ε, unit↑))];
  |}
  .

  Definition main: Mod.t := {|
    Mod.get_modsem := fun _ => mainSem;
    Mod.sk := [("Main", Sk.Gfun)];
  |}
  .
End PROOF.
