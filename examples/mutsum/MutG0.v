Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import TODO.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  (***
    g(n) := if (n == 0) then 0 else (n + f(n-1))
  ***)
  Definition gF: list val -> itree Es val :=
    fun varg =>
      `n: Z <- (pargs [Tint] varg)?;;
      assume (intrange_64 n);;;
      if dec n 0%Z
      then Ret (Vint 0)
      else
        (m <- ccall "f" [Vint (n - 1)];;
        r <- (vadd (Vint n) m)?;;
        Ret r).

  Definition GSem: ModSem.t := {|
    ModSem.fnsems := [("g", cfun gF)];
    ModSem.mn := "G";
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}
  .

  Definition G: Mod.t := {|
    Mod.get_modsem := fun _ => GSem;
    Mod.sk := [("g", Sk.Gfun)];
  |}
  .
End PROOF.
