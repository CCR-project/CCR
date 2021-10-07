Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.


(***
f.f(n) {
  if (n == 42) { r := ... }
  else {
    if (n == 0) {
      r := 0
    } else if (n < 0) {
      log.log("error")
      r := -1
    } else {
      r := 2 + call g.g(n)
    }
  }
  r
}
***)

Section PROOF.

  Definition fF: list val -> itree Es val :=
    fun varg =>
      `n: Z <- (pargs [Tint] varg)?;;
      assume (intrange_64 n);;;
      if dec n 0%Z
      then Ret (Vint 0)
      else
        (assume (intrange_64 (n - 1));;;
        m <- ccallU "g" [Vint (n - 1)];;
        assume (wf_val m);;;
        r <- (vadd (Vint n) m)?;;
        assume (wf_val r);;;
        Ret r).

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
