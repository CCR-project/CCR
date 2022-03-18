Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import IntroHeader.
Require Import HoareDef.

Set Implicit Arguments.

Local Open Scope nat_scope.


Section PROOF.

  Definition fF: list val -> itree Es val :=
    fun varg =>
      n <- trigger (Take _);;
      assume(varg = [Vint (Z.of_nat n)] /\ n < max);;;
      (Ncall (1 <= n < max /\ (ord_lt (g_measure n) (f_measure n)))
             (fun r => r = Vint (Z.of_nat (5 * n - 2))) "g" [Vint (Z.of_nat n)]);;;
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
