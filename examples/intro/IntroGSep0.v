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
   local usable = true
   if (usable) { Log.log("error"); -1 }        -> expire 지우기, spec -> termination 증명
   else { r = F.f(n-1); usable = false; 3 + r }
}

G.g(n) {
   local usable = true
   r := if (usable) { Log.log("error"); -1 }        -> expire 지우기, spec -> termination 증명
        else { 3 + F.f(n-1) }
   usable = false;
   r
}
***)

Section PROOF.

  Definition gF: list val -> itree Es val :=
    fun varg =>
      `n: Z <- (pargs [Tint] varg)?;;
      p0 <- trigger (PGet);;
      p0 <- p0↓?;;
      if (p0: bool)
      then r <- ccallU "f" [Vint (n - 1)];; res <- (vadd (Vint 3) r)?;; trigger (PPut false↑);;; Ret res
      else `_: val <- ccallU "log" [Vint n];; Ret (Vint (- 1))
  .

  Definition GSem: ModSem.t := {|
    ModSem.fnsems := [("g", cfunU gF)];
    ModSem.mn := "G";
    ModSem.initial_st := true↑;
  |}
  .

  Definition G: Mod.t := {|
    Mod.get_modsem := fun _ => GSem;
    Mod.sk := [("g", Sk.Gfun)];
  |}
  .

End PROOF.
