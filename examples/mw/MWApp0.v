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
      then trigger (Syscall "print" [Vint (- 1)]↑ top1);;; Ret Vundef
      else `_: val <- ccallU "put" [Vint 0; Vint 42];; Ret Vundef
  .

  Definition runF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      initialized <- pget;;
      if negb (initialized: bool)
      then trigger (Syscall "print" [Vint (- 1)]↑ top1);;; Ret Vundef
      else `v: val <- ccallU "get" [Vint 0];; trigger (Syscall "print" [v]↑ top1);;; Ret Vundef
  .

  Definition AppSem: ModSem.t := {|
    ModSem.fnsems := [("init", cfunU initF); ("run", cfunU runF)];
    ModSem.mn := "App";
    ModSem.initial_st := false↑;
  |}
  .

  Definition App: Mod.t := {|
    Mod.get_modsem := fun _ => AppSem;
    Mod.sk := [("init", Sk.Gfun); ("run", Sk.Gfun)];
  |}
  .

End PROOF.
