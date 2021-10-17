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

  (* Definition ASSUME (P: iProp): itree Es unit := *)
  (*   ri <- trigger (Take _);; *)
  (*   assume(P ri);;; *)
  (*   rm0 <- pget;; rm1 <- trigger (Take _);; assume(rm1 = rm0 ⋅ ri ∧ URA.wf rm1);;; pput rm1;;; *)
  (*   Ret tt *)
  (* . *)

  (* Definition GUARANTEE (Q: iProp): itree Es unit := *)
  (*   ro <- trigger (Choose _);; *)
  (*   guarantee(Q ro);;; *)
  (*   rm0 <- pget;; rm1 <- trigger (Choose _);; guarantee(rm1 ⋅ ro = rm0);;; *)
  (*   Ret tt *)
  (* . *)

  (* Definition initF: list val -> itree Es val := *)
  (*   fun varg => _ <- (pargs [] varg)?;; *)
  (*     ASSUME(OwnM AppInit);;; *)

  (*     GUARANTEE(⌜True⌝%I);;; *)
  (*     `_: val <- ccallU "put" [Vint 0; Vint 42];; *)
  (*     ASSUME(⌜True⌝%I);;; *)

  (*     GUARANTEE(OwnM AppRun);;; *)

  (*     Ret Vundef *)
  (* . *)


  (***
     var ri := Take
     assume(P ri)
     rf := take(rf + rm + ri)
   ***)

  (***
     var (rm, ro) := Choose
     guarantee(Q ro)
     rf := choose (rf - rm - ro)
   ***)

  Definition ASSUME rf0 (P: AppRA -> Prop): itree Es _ :=
    ri <- trigger (Take _);;
    assume(P ri);;;
    rm <- pget;; rf1 <- trigger (Take _);; assume(rf1 = rm ⋅ ri ⋅ rf0 ∧ URA.wf rf1);;;
    Ret rf1
  .

  Definition GUARANTEE rf0 (Q: AppRA -> Prop): itree Es _ :=
    '(rm, ro, rf1) <- trigger (Choose _);;
    guarantee(Q ro);;;
    guarantee(rm ⋅ ro ⋅ rf1 = rf0);;; pput rm;;;
    Ret rf1
  .

  Definition initF: list val -> itree Es val :=
    fun varg => _ <- (pargs [] varg)?;;
      let rf := ε in
      rf <- (ASSUME rf (eq AppInit));;

      rf <- (GUARANTEE rf top1);;
      `_: val <- ccallU "put" [Vint 0; Vint 42];;
      rf <- (ASSUME rf top1);;

      rf <- (GUARANTEE rf (eq AppRun));;

      Ret Vundef
  .

  (* Definition runF: list val -> itree Es val := *)
  (*   fun varg => _ <- (pargs [] varg)?;; *)
  (*     ri <- trigger (Take _);; *)
  (*     assume(ri = AppInit);;; *)
  (*     `rm0: AppRA <- pget;; rm1 <- trigger (Take _);; assume(rm1 = rm0 ⋅ ri ∧ URA.wf rm1);;; pput rm1;;; *)

  (*     `v: val <- ccallU "get" [Vint 0];; trigger (Syscall "print" [v]↑ top1);;; *)

  (*     ro <- trigger (Choose _);; *)
  (*     guarantee(ro = AppRun);;; *)
  (*     rm2 <- pget;; rm3 <- trigger (Choose _);; guarantee(rm3 ⋅ ro = rm2);;; *)

  (*     Ret Vundef *)
  (* . *)

  Definition runF: list val -> itree Es val :=
    fun varg => _ <- (pargs [] varg)?;;
      let rf := ε in
      rf <- (ASSUME rf (eq AppRun));;

      rf <- (GUARANTEE rf top1);;
      `v: val <- ccallU "get" [Vint 0];; trigger (Syscall "print" [v]↑ top1);;;
      rf <- (ASSUME rf top1);;

      rf <- GUARANTEE rf (eq AppRun);;
      Ret Vundef
  .

  Definition AppSem: ModSem.t := {|
    ModSem.fnsems := [("init", cfunU initF); ("run", cfunU runF)];
    ModSem.mn := "App";
    ModSem.initial_st := (AppInitX)↑;
  |}
  .

  Definition App: Mod.t := {|
    Mod.get_modsem := fun _ => AppSem;
    Mod.sk := [("init", Sk.Gfun); ("run", Sk.Gfun)];
  |}
  .

End PROOF.
