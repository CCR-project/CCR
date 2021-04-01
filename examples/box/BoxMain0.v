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

  Definition mainF: Any.t -> itree Es Any.t :=
    fun _ =>
      trigger (Call "set" [Vint 10]↑);;
      r <- trigger (Call "get" ([]: list val)↑);;
      `r: val <- r↓?;;
      Ret r↑
  .

  Definition MainSem: ModSemL.t := {|
    ModSemL.fnsems := [("main", mainF)];
    ModSemL.initial_mrs := [("Main", ε)];
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
