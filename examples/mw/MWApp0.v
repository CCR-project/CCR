Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import MWHeader.

Set Implicit Arguments.



Section PROOF.

  (* Definition pget A: itree Es A := (p0 <- trigger PGet;; `p0: A <- p0↓ǃ;; Ret p0). *)
  (* Definition pput A (p0: A) := (trigger (PPut p0↑)). *)
  Notation pget := (p0 <- trigger PGet;; p0 <- p0↓ǃ;; Ret p0) (only parsing).
  Notation pput p0 := (trigger (PPut p0↑)) (only parsing).

  Definition initF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      initialized <- pget;;
      if (initialized: bool)
      then syscallU "print" [(- 1)%Z];;; Ret Vundef
      else `_: val <- ccallU "MW.put" [Vint 0; Vint 42];; pput true;;; Ret Vundef
  .

  Definition runF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      initialized <- pget;;
      if negb (initialized: bool)
      then syscallU "print" [(- 1)%Z];;; Ret Vundef
      else `v: val <- ccallU "MW.get" [Vint 0];; v <- (pargs [Tint] [v])?;; assume(intrange_64 v);;; syscallU "print" [v];;; Ret Vundef
  .

  Definition AppSem: ModSem.t := {|
    ModSem.fnsems := [("App.init", cfunU initF); ("App.run", cfunU runF)];
    ModSem.mn := "App";
    ModSem.initial_st := false↑;
  |}
  .

  Definition App: Mod.t := {|
    Mod.get_modsem := fun _ => AppSem;
    Mod.sk := [("App.init", Sk.Gfun); ("App.run", Sk.Gfun); ("initialized", Sk.Gvar 0)];
  |}
  .

End PROOF.
