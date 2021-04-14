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
  Context `{@GRA.inG memRA Σ}.

  (* TODO: move it to better place *)
  Definition Vbool (b: bool): val :=
    if b then Vint 0 else Vint 1.

  Definition compareF (skenv: SkEnv.t): list val -> itree Es val :=
    fun varg =>
      '(n0, n1) <- (pargs [Tint; Tint] varg)?;;
      if (Z_le_gt_dec n0 n1)
      then Ret (Vint 0)
      else Ret (Vint 1)
  .

  Definition wrapF (skenv: SkEnv.t): list val -> itree Es val :=
    fun varg =>
      '(n0, (n1, fb)) <- (pargs [Tint; Tint; Tblk] varg)?;;
      fn <- (skenv.(SkEnv.blk2id) fb)?;;
      ccall fn [Vint n0; Vint n1].

  Definition mainF (skenv: SkEnv.t): list val -> itree Es val :=
    fun varg =>
      n0 <- trigger (Choose Z);;
      n1 <- trigger (Choose Z);;
      fn <- (skenv.(SkEnv.id2blk) "compare")?;;
      r0 <- ccall "wrap" [Vint n0; Vint n1];; r0 <- (unint r0)?;;
      r1 <- ccall "wrap" [Vint n0; Vint n1];; r1 <- (unint r1)?;;
      assume (r0 = r1);;
      Ret Vundef
  .

  Definition CompareSem (skenv: SkEnv.t): ModSem.t := {|
    ModSem.fnsems := [("main", cfun (mainF skenv)); ("compare", cfun (compareF skenv)); ("wrap", cfun (wrapF skenv))];
    ModSem.mn := "Main";
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Compare: Mod.t := {|
    Mod.get_modsem := fun skenv => CompareSem skenv;
    Mod.sk := [("compare", Sk.Gfun)];
  |}
  .
End PROOF.
