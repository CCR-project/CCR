Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB IPM.
Require Import MapHeader.

Set Implicit Arguments.


(*** module M Map
private data: List int64 := []

def init(sz: int64 ) ≡
  data := List.repeat(sz, 0)

def set(k: int64 , v: int64 ) ≡
  data := data[k ← v]?
  print("set"+str(k)+str(r))

def get(k: int64 ) ≡
  var r := data[k]?
  print("get"+str(k)+str(r))
  return r
***)

Section M.
  Context `{@GRA.inG MapRA0 Σ}.

  Let Es := (hAPCE +' Es).

  Definition initF: list val -> itree Es val :=
    fun varg =>
      `sz: Z <- (pargs [Tint] varg)?;;
      _ <- pput (List.repeat 0%Z (Z.to_nat sz));;;
      Ret Vundef
  .

  Definition setF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      data <- pget;; data <- (set_nth (Z.to_nat k) data v)?;;
      _ <- pput data;;;
      trigger (Syscall "print" (k↑) (fun _ => True));;;
      trigger (Syscall "print" (v↑) (fun _ => True));;;
      Ret Vundef
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      data <- pget;;
      r <- (nth_error data (Z.to_nat k))?;;;
      trigger (Syscall "print" (k↑) (fun _ => True));;;
      trigger (Syscall "print" (r↑) (fun _ => True));;;
      Ret (Vint r)
  .

  Definition MapSbtbM: list (string * fspecbody) :=
    [("init", mk_specbody init_specM (cfunU initF));
     ("set", mk_specbody set_specM (cfunU setF));
     ("get", mk_specbody get_specM (cfunU getF))].

  Definition SMapSem: SModSem.t := {|
    SModSem.fnsems := MapSbtbM;
    SModSem.mn := "Map";
    SModSem.initial_mr := ε;
    SModSem.initial_st := ([]: list Z)↑;
  |}
  .

  Definition SMap: SMod.t := {|
    SMod.get_modsem := fun _ => SMapSem;
    SMod.sk := [("init", Sk.Gfun); ("set", Sk.Gfun); ("get", Sk.Gfun)];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Map: Mod.t := (SMod.to_tgt GlobalStb SMap).
End M.
