Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
(* Require Import HoareDef. *)
Require Import MWHeader.
Require Import STB IPM.

Set Implicit Arguments.



Section PROOF.

  Context `{@GRA.inG AppRA Σ}.

  Notation pget := (p0 <- trigger PGet;; p0 <- p0↓ǃ;; Ret p0) (only parsing).
  Notation pput p0 := (trigger (PPut p0↑)) (only parsing).

  Definition initF: list val -> itree Es val :=
    fun varg => _ <- (pargs [] varg)?;;
      ri <- trigger (Take _);;
      assume(ri = AppInit);;;
      rm0 <- pget;; rm1 <- trigger (Take _);; assume(rm1 = rm0 ⋅ rm1 ∧ URA.wf rm1);;; pput rm1;;;

      `_: val <- ccallU "put" [Vint 0; Vint 42];;

      ro <- trigger (Choose _);;
      guarantee(ro = AppRun);;;
      rm2 <- pget;; rm3 <- trigger (Choose _);; guarantee(rm3 ⋅ ro = rm2);;;

      Ret Vundef
  .

  Definition runF: list val -> itree Es val :=
    fun varg => _ <- (pargs [] varg)?;;
      ri <- trigger (Take _);;
      assume(ri = AppInit);;;
      rm0 <- pget;; rm1 <- trigger (Take _);; assume(rm1 = rm0 ⋅ rm1 ∧ URA.wf rm1);;; pput rm1;;;

      `v: val <- ccallU "get" [Vint 0];; trigger (Syscall "print" [v]↑ top1);;;

      ro <- trigger (Choose _);;
      guarantee(ro = AppRun);;;
      rm2 <- pget;; rm3 <- trigger (Choose _);; guarantee(rm3 ⋅ ro = rm2);;;

      Ret Vundef
  .

  Definition AppSem: ModSem.t := {|
    ModSem.fnsems := [("init", cfunU initF); ("run", cfunU runF)];
    ModSem.mn := "App";
    ModSem.initial_st := (GRA.embed AppInitX)↑;
  |}
  .

  Definition App: Mod.t := {|
    Mod.get_modsem := fun _ => AppSem;
    Mod.sk := [("init", Sk.Gfun); ("run", Sk.Gfun)];
  |}
  .

End PROOF.
