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
F.f(n) {
  if (n < 0) {
    r := -1
  } else if (n == 0) {
    r := ...
  } else {
    r := 5 * Ncall P Q G.g(n)
  }
  r
}
***)

Section PROOF.

  Definition Ncall X Y P Q (f: string) (x: X): itree Es Y :=
    guarantee(P x);;;
    `b: bool <- trigger (Choose bool);;
    r <- if b then ccallU f x else trigger (Choose _);;
    assume(Q r);;;
    Ret r
  .

  Definition fF: list val -> itree Es val :=
    fun varg =>
      `n: Z <- (pargs [Tint] varg)?;;
      assume (intrange_64 n);;;
      if (n <? 0)%Z
      then Ret (Vint (- 1))
      else if (n =? 0)%Z
           then Ret (Vint 0)
           else (Ncall (fun x => (0 <= x < Z.of_nat max)%Z) (fun r => r = Vint (5 * n - 2)) "g" n)
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
