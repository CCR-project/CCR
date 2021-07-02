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

  Definition main_body: list val -> itree Es val :=
    fun _ => (ccallU "echo" ([]: list val))
  .

  Definition MainSem: ModSem.t := {|
    ModSem.fnsems := [("main", cfunU main_body)];
    ModSem.mn := "main";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
