Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Definition parg: list val -> option val := (@hd_error _).

Section PROOF.

  Context `{Σ: GRA.t}.

  (***
    g(n) := if (n == 0) then 0 else (n + f(n-1))
  ***)
  Definition gF: list val -> itree Es val :=
    fun varg =>
      `n: val <- (parg varg)?;; `n: Z <- (unint n)?;;
      if dec n 0%Z
      then Ret (Vint 0)
      else
        (m <- ccall "f" [Vint (n - 1)];;
        r <- (vadd (Vint n) m)?;;
        Ret r).

  Definition GSem: ModSem.t := {|
    ModSem.fnsems := [("g", cfun gF)];
    ModSem.initial_mrs := [("G", (ε, tt↑))];
  |}
  .

  Definition G: Mod.t := {|
    Mod.get_modsem := fun _ => GSem;
    Mod.sk := [("g", Sk.Gfun)];
  |}
  .
End PROOF.
