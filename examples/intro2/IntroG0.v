Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import IntroHeader.

Set Implicit Arguments.



(***
G.g(n) {
   3 + F.f(n-1)
}
***)

Section PROOF.

  Definition gF: list val -> itree Es val :=
    fun varg =>
      `n: Z <- (pargs [Tint] varg)?;;
      r <- ccallU "f" [Vint (n - 1)];; res <- (vadd (Vint 3) r)?;; Ret res
  .

  Definition GSem: ModSem.t := {|
    ModSem.fnsems := [("g", cfunU gF)];
    ModSem.mn := "G";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition G: Mod.t := {|
    Mod.get_modsem := fun _ => GSem;
    Mod.sk := [("g", Sk.Gfun)];
  |}
  .

End PROOF.
