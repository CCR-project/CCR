Require Import Coqlib.
Require Import ImpPrelude ITreelib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import STB.

Set Implicit Arguments.



Section PROOF.
  Definition succF {E} `{callE -< E} `{eventE -< E}: list val -> itree E val :=
    fun varg =>
      n <- ((pargs [Tint] varg)?);;
      Ret (Vint (n + 1)).

  Definition addF {E} `{callE -< E} `{eventE -< E} (skenv: SkEnv.t): list val -> itree E val :=
    fun varg =>
      '(n, m) <- ((pargs [Tint; Tint] varg)?);;
      fb <- ((skenv.(SkEnv.id2blk) "succ")?);;
      ccallU "repeat" [Vptr fb 0; Vint m; Vint n]
  .

  Definition AddSem (sk: Sk.t): ModSem.t := {|
    ModSem.fnsems :=
      [("succ", cfunU succF); ("add", cfunU (addF (Sk.load_skenv sk)))];
    ModSem.mn := "Add";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Add: Mod.t := {|
    Mod.get_modsem := AddSem;
    Mod.sk := [("succ", Sk.Gfun); ("add", Sk.Gfun)];
  |}
  .
End PROOF.
