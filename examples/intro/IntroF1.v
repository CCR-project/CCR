Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import IntroHeader.

Set Implicit Arguments.



Section PROOF.

  Definition fF: list val -> itree Es val :=
    fun varg =>
      n <- trigger (Take _);;
      assume(varg = [Vint (Z.of_nat n)] /\ n < max);;;
      (Ncall (n < max) (fun r => r = Vint (Z.of_nat (5 * n - 2))) "g" [Vint (Z.of_nat n)]);;;
      r <- trigger (Choose _);;
      guarantee(r = (Vint (Z.of_nat (5 * n))));;;
      Ret r
  .

  Definition FSem: ModSem.t := {|
    ModSem.fnsems := [("f", cfunU fF)];
    ModSem.mn := "F";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition F: Mod.t := {|
    Mod.get_modsem := fun _ => FSem;
    Mod.sk := [("f", Sk.Gfun)];
  |}
  .

End PROOF.
