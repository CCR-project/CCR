Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Set Implicit Arguments.






Section CANNON.
  Definition div (n m: Z): option Z :=
    if Z_zerop m then None else Some (Z.div n m).

  Definition fire_body {E} `{callE -< E} `{pE -< E} `{eventE -< E}
    : list val -> itree E Z :=
    fun args =>
      powder <- trigger PGet;; powder <- powder↓?;;
      r <- (div 1 powder)?;;
      _ <- trigger (Syscall "print" [r]↑ top1);;
      _ <- trigger (PPut r↑);;
      Ret r
  .

  Definition CannonSem: ModSem.t := {|
    ModSem.fnsems := [("fire", cfunU fire_body)];
    ModSem.mn := "Cannon";
    ModSem.initial_st := (1: Z)%Z↑;
  |}
  .

  Definition Cannon: Mod.t := {|
    Mod.get_modsem := fun _ => CannonSem;
    Mod.sk := [("fire", Sk.Gfun)];
  |}
  .
End CANNON.
