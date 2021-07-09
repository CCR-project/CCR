Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Mem1.

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.

  Definition fibF (skenv: SkEnv.t): list val -> itree Es val :=
    fun varg =>
      '(fb, n) <- (pargs [Tblk; Tint] varg)?;;
      fn <- (skenv.(SkEnv.blk2id) fb)?;;
      assume(intrange_64 n);;;
      if(Z_le_gt_dec n 1)
      then Ret (Vint 1)
      else
        `n0: val <- ccallU fn [Vint (n - 1)];; `n0: Z <- (unint n0)?;;
        `n1: val <- ccallU fn [Vint (n - 2)];; `n1: Z <- (unint n1)?;;
        Ret (Vint (n0 + n1)).

  Definition mainF (skenv: SkEnv.t): list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      fibb <- (skenv.(SkEnv.id2blk) "fib")?;;
      `fb: val <- ccallU "knot" [Vptr fibb 0];; `fb: mblock <- (unblk fb)?;;
      fn <- (skenv.(SkEnv.blk2id) fb)?;;
      ccallU fn [Vint 10].

  Definition MainSem (skenv: SkEnv.t): ModSem.t := {|
    ModSem.fnsems := [("fib", cfunU (fibF skenv)); ("main", cfunU (mainF skenv))];
    ModSem.mn := "Main";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun skenv => MainSem (Sk.load_skenv skenv);
    Mod.sk := [("fib", Sk.Gfun)];
  |}
  .
End PROOF.
