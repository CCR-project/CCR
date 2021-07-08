Require Import Coqlib.
Require Import ImpPrelude ITreelib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import STB.

Set Implicit Arguments.



Section PROOF.
  Definition repeatF {E} `{callE -< E} `{eventE -< E} (skenv: SkEnv.t): list val -> itree E val :=
    fun varg =>
      '(fb, (n, x)) <- (pargs [Tblk; Tint; Tint] varg)?;;
      assume(intrange_64 n);;;
      if (Z_lt_le_dec n 1)
      then Ret (Vint x)
      else
        fn <- (skenv.(SkEnv.blk2id) fb)?;;
        v <- ccallU fn [Vint x];;
        ccallU "repeat" [Vptr fb 0; Vint (n - 1); v].

  Definition RepeatSem (sk: Sk.t): ModSem.t := {|
    ModSem.fnsems := [("repeat", cfunU (repeatF (Sk.load_skenv sk: SkEnv.t)))];
    ModSem.mn := "Repeat";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Repeat: Mod.t := {|
    Mod.get_modsem := RepeatSem;
    Mod.sk := [("repeat", Sk.Gfun)];
  |}
  .
End PROOF.
