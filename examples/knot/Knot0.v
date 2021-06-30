Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import TODOYJ.

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.

  Definition knotF (skenv: SkEnv.t): list val -> itree Es val :=
    fun varg =>
      'fb <- (pargs [Tblk] varg)?;;
      blk <- (skenv.(SkEnv.id2blk) "_f")?;;
      `_: val <- ccall "store" [Vptr blk 0; Vptr fb 0];;
      rb <- (skenv.(SkEnv.id2blk) "rec")?;;
      Ret (Vptr rb 0).

  Definition recF (skenv: SkEnv.t): list val -> itree Es val :=
    fun varg =>
      'n <- (pargs [Tint] varg)?;;
      blk <- (skenv.(SkEnv.id2blk) "_f")?;;
      `fb: val <- ccall "load" [Vptr blk 0];; fb <- (unblk fb)?;;
      fn <- (skenv.(SkEnv.blk2id) fb)?;;
      rb <- (skenv.(SkEnv.id2blk) "rec")?;;
      ccall fn [Vptr rb 0; Vint n].

  Definition KnotSem (sk: Sk.t): ModSem.t := {|
    ModSem.fnsems := [("rec", cfun (recF sk)); ("knot", cfun (knotF sk))];
    ModSem.mn := "Knot";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Knot: Mod.t := {|
    Mod.get_modsem := fun skenv => KnotSem skenv;
    Mod.sk := [("rec", Sk.Gfun); ("_f", Sk.Gvar 0)];
  |}
  .
End PROOF.
