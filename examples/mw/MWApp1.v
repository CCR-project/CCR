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
Require Import HoareDef STB IPM.

Set Implicit Arguments.



Section PROOF.

  Context `{@GRA.inG AppRA.t Σ}.

  Notation pget := (p0 <- trigger PGet;; p0 <- p0↓ǃ;; Ret p0) (only parsing).
  Notation pput p0 := (trigger (PPut p0↑)) (only parsing).

  (* Definition ASSUME rf0 (P: AppRA.t -> Prop): itree Es _ := *)
  (*   ri <- trigger (Take _);; *)
  (*   assume(P ri);;; *)
  (*   rm <- pget;; rf1 <- trigger (Take _);; assume(rf1 = rm ⋅ ri ⋅ rf0 ∧ URA.wf rf1);;; *)
  (*   Ret rf1 *)
  (* . *)

  (* Definition GUARANTEE rf0 (Q: AppRA.t -> Prop): itree Es _ := *)
  (*   '(rm, ro, rf1) <- trigger (Choose _);; *)
  (*   guarantee(Q ro);;; *)
  (*   guarantee(rm ⋅ ro ⋅ rf1 = rf0);;; pput rm;;; *)
  (*   Ret rf1 *)
  (* . *)

  (*** OLD CODE ***)
  (* Definition initF: list val -> itree Es val := *)
  (*   fun varg => _ <- (pargs [] varg)?;; *)
  (*     let rf := ε in *)
  (*     rf <- (ASSUME rf (eq Init));; *)

  (*     rf <- (GUARANTEE rf top1);; *)
  (*     `_: val <- ccallU "put" [Vint 0; Vint 42];; *)
  (*     rf <- (ASSUME rf top1);; *)

  (*     rf <- (GUARANTEE rf (eq Run));; *)

  (*     Ret Vundef *)
  (* . *)

  (* Definition runF: list val -> itree Es val := *)
  (*   fun varg => _ <- (pargs [] varg)?;; *)
  (*     let rf := ε in *)
  (*     rf <- (ASSUME rf (eq Run));; *)

  (*     rf <- (GUARANTEE rf top1);; *)
  (*     `v: val <- ccallU "get" [Vint 0];; trigger (Syscall "print" [v]↑ top1);;; *)
  (*     rf <- (ASSUME rf top1);; *)

  (*     rf <- GUARANTEE rf (eq Run);; *)
  (*     Ret Vundef *)
  (* . *)

  Let Es := (hAPCE +' Es).

  Definition initF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      `_: val <- ccallU "put" ([Vint 0; Vint 42]);;
      Ret Vundef
  .

  Definition runF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      `r: val <- ccallU "get" ([Vint 0]);;
      r <- (pargs [Tint] [r])?;; syscallU "print" [r];;;
      Ret Vundef
  .

  Definition AppSbtb: list (string * fspecbody) :=
    [("init", mk_specbody init_spec1 (cfunU initF));
    ("run", mk_specbody run_spec1 (cfunU runF))
    ].

  Definition SAppSem: SModSem.t := {|
    SModSem.fnsems := AppSbtb;
    SModSem.mn := "App";
    SModSem.initial_mr := (GRA.embed Run);
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SApp: SMod.t := {|
    SMod.get_modsem := fun _ => SAppSem;
    SMod.sk := [("init", Sk.Gfun); ("run", Sk.Gfun)];
  |}
  .

  Definition App: Mod.t := (SMod.to_tgt (fun _ => to_stb App1Stb) SApp).

End PROOF.
