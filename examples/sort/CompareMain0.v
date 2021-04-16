Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Mem1.
Require Import TODOYJ TODO CompareHeader.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.

  Definition compareF (skenv: SkEnv.t): list val -> itree Es val :=
    fun varg =>
      '(n0, n1) <- (pargs [Tint; Tint] varg)?;;
      Ret (Vint (mycmp n0 n1))
  .

  Definition mainF (skenv: SkEnv.t): list val -> itree Es val :=
    fun varg =>
      n0 <- trigger (Choose Z);;
      n1 <- trigger (Choose Z);;
      blk <- (skenv.(SkEnv.id2blk) "compare")?;;
      r0 <- ccall "wrap" [Vint n0; Vint n1; Vptr blk 0];; r0 <- (unint r0)?;;
      r1 <- ccall "wrap" [Vint n0; Vint n1; Vptr blk 0];; r1 <- (unint r1)?;;
      assume (r0 = r1);;
      Ret Vundef
  .

  Definition MainSem (skenv: SkEnv.t): ModSem.t := {|
    ModSem.fnsems := [("main", cfun (mainF skenv)); ("compare", cfun (compareF skenv))];
    ModSem.mn := "Main";
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun skenv => MainSem skenv;
    Mod.sk := [("compare", Sk.Gfun)];
  |}
  .
End PROOF.

Definition cmpspecs: list (gname * (Z -> Z -> Z)) := [("compare", mycmp)].
