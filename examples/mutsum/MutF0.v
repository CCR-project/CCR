Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.

Set Implicit Arguments.



Section PROOF.

  (***
    f(n) := if (n == 0) then 0 else (n + g(n-1))
  ***)
  Definition fF: list val -> itree Es val :=
    fun varg =>
      `n: Z <- (pargs [Tint] varg)?;;
      assume (intrange_64 n);;;
      if dec n 0%Z
      then Ret (Vint 0)
      else
        (assume (intrange_64 (n - 1));;;
        m <- ccall "g" [Vint (n - 1)];;
        assume (wf_val m);;;
        r <- (vadd (Vint n) m)?;;
        assume (wf_val r);;;
        Ret r).

  Definition FSem: ModSem.t := {|
    ModSem.fnsems := [("f", cfun fF)];
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
