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

  Definition wrapF (skenv: SkEnv.t): list val -> itree Es val :=
    fun varg =>
      '(n0, (n1, fb)) <- (pargs [Tint; Tint; Tblk] varg)?;;
      fn <- (skenv.(SkEnv.blk2id) fb)?;;
      ccall fn [Vint n0; Vint n1].

  Definition WrapSem (skenv: SkEnv.t): ModSem.t := {|
    ModSem.fnsems := [("wrap", cfun (wrapF skenv))];
    ModSem.mn := "Wrap";
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Wrap: Mod.t := {|
    Mod.get_modsem := fun skenv => WrapSem skenv;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
