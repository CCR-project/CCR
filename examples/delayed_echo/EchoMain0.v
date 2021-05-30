Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import TODOYJ.

Set Implicit Arguments.






Section PROOF.

  Context `{Σ: GRA.t}.

  Definition mainF: list val -> itree Es val :=
    fun _ =>
      `n: val    <- (ccall "echo" ([]: list val));;
      Ret Vundef
  .

  Definition MainSem: ModSem.t := {|
    ModSem.fnsems := [("main", cfun mainF)];
    ModSem.mn := "main";
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
