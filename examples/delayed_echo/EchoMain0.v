Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.






Section PROOF.

  Context `{Σ: GRA.t}.

  Definition mainF: list val -> itree Es val :=
    fun _ =>
      `n: val    <- (ccall "echo" ([]: list val));;
      Ret Vundef
  .

  Definition MainSem: ModSemL.t := {|
    ModSemL.fnsems := [("main", cfun mainF)];
    ModSemL.initial_mrs := [("main", (ε, tt↑))];
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
