Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.

Set Implicit Arguments.



Section PROOF.
  Definition mulF: Z * Z -> itree Es Z :=
    fun '(a, b) =>
      (ITree.iter
         (fun '(a, res) =>
            if(0 <? a)%Z
            then Ret (inl (a - 1, res + b))
            else Ret (inr res))
         (a, 0))%Z.

  Definition MulSem: ModSem.t := {|
    ModSem.fnsems := [("mul", cfunU mulF)];
    ModSem.mn := "Mul";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Mul: Mod.t := {|
    Mod.get_modsem := fun _ => MulSem;
    Mod.sk := [("mul", Sk.Gfun)];
  |}
  .
End PROOF.
