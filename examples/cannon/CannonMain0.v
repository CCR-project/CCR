Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Set Implicit Arguments.






Section CANNONMAIN.
  Variable num_fire: nat.

  Fixpoint main_repeat {E} `{callE -< E} `{eventE -< E} (n: nat): itree E unit :=
    match n with
    | 0 =>
      Ret tt
    | S n' =>
      `r: Z <- ccallU "fire" ([]: list val);;
      _ <- trigger (Syscall "print" [r]↑ top1);;
      main_repeat n'
    end.

  Definition main_body {E} `{callE -< E} `{eventE -< E}: list val -> itree E unit :=
    fun args =>
      main_repeat num_fire
  .

  Definition MainSem: ModSem.t := {|
    ModSem.fnsems := [("main", cfunU main_body)];
    ModSem.mn := "Main";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := [("main", Sk.Gfun)];
  |}
  .
End CANNONMAIN.
