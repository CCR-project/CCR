Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import MWHeader.
Require Import PCM.
Require Import HoareDef OpenDef STB.
Require Import Mem1.

Set Implicit Arguments.



Section PROOF.

  (* Definition pget A: itree Es A := (p0 <- trigger PGet;; `p0: A <- p0↓ǃ;; Ret p0). *)
  (* Definition pput A (p0: A) := (trigger (PPut p0↑)). *)
  Notation pget := (p0 <- trigger PGet;; p0 <- p0↓ǃ;; Ret p0) (only parsing).
  Notation pput p0 := (trigger (PPut p0↑)) (only parsing).

  Notation check_lock := (p0 <- trigger PGet;; if (Any.split p0) then triggerUB else Ret tt) (only parsing).
  Notation lAPC := (p0 <- trigger PGet;; _ <- trigger (PPut (Any.pair tt↑ p0));;; trigger (PPut p0))
                     (only parsing).

  Let Es := (hAPCE +' Es).

  Definition initF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      check_lock;;;
      lAPC;;;
      initialized <- pget;;
      if (initialized: bool)
      then syscallU "print" [(- 1)%Z];;; Ret Vundef
      else `_: val <- ccallU "put" [Vint 0; Vint 42];; lAPC;;; pput true;;; Ret Vundef
  .

  Definition runF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      check_lock;;;
      lAPC;;;
      initialized <- pget;;
      if negb (initialized: bool)
      then syscallU "print" [(- 1)%Z];;; Ret Vundef
      else `v: val <- ccallU "get" [Vint 0];; v <- (pargs [Tint] [v])?;; assume(intrange_64 v);;; syscallU "print" [v];;; Ret Vundef
  .

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition Appsbtb: list (string * kspecbody) :=
    [("init", ksb_trivial (cfunU initF)); ("run", ksb_trivial (cfunU runF))].

  Definition AppStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun ksb => ksb.(ksb_fspec): fspec)) Appsbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition KAppSem ske: KModSem.t := {|
    KModSem.fnsems := Appsbtb;
    KModSem.mn := "App";
    KModSem.initial_mr := GRA.embed (var_points_to ske "initialized" (Vint 0)) ;
    KModSem.initial_st := false↑;
  |}
  .

  (* Definition MWSem (stb: gname -> option fspec): ModSem.t := *)
  (*   KModSem.transl_tgt stb KMWSem. *)

  Definition KApp: KMod.t := {|
    KMod.get_modsem := fun sk => KAppSem (Sk.load_skenv sk);
    KMod.sk := []
  |}
  .

  Definition App (stb: Sk.t -> gname -> option fspec): Mod.t := (KMod.transl_tgt stb KApp).

End PROOF.
Global Hint Unfold AppStb: stb.
