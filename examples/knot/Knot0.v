Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Mem1.
Require Import TODOYJ TODO.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.

  Definition knotF (skenv: SkEnv.t): list val -> itree Es val :=
    fun varg =>
      'fb <- (pargs [Tblk] varg)?;;
      trigger (PPut (Some fb)↑);;
      rb <- (skenv.(SkEnv.id2blk) "rec")?;;
      Ret (Vptr rb 0).

  Definition recF (skenv: SkEnv.t): list val -> itree Es val :=
    fun varg =>
      'n <- (pargs [Tint] varg)?;;
      fb <- trigger (PGet);; `fb: option block <- fb↓?;; `fb: block <- fb?;;
      fn <- (skenv.(SkEnv.blk2id) fb)?;;
      rb <- (skenv.(SkEnv.id2blk) "rec")?;;
      ccall fn [Vptr rb 0; Vint n].

  Definition KnotSem (skenv: SkEnv.t): ModSem.t := {|
    ModSem.fnsems := [("rec", cfun (recF skenv)); ("knot", cfun (knotF skenv))];
    ModSem.mn := "Knot";
    ModSem.initial_mr := ε;
    ModSem.initial_st := (None: option block)↑;
  |}
  .

  Definition Knot: Mod.t := {|
    Mod.get_modsem := fun skenv => KnotSem skenv;
    Mod.sk := [("rec", Sk.Gfun)];
  |}
  .
End PROOF.
