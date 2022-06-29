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


(*** module A Map
private map: int64 -> int64

def init(sz: int64 ) ≡
  map := (fun k => 0)

def set(k: int64 , v: int64map := map[k ← v]
  print("set"+str(k)+str(r))

def get(k: int64 ): int64 ≡
  var r := map[k]
  print("get"+str(k)+str(r))
  return r
***)

Section A.
  Context `{@GRA.inG MapRA0 Σ}.
  Context `{@GRA.inG MapRA1 Σ}.

  Let Es := (hAPCE +' Es).

  Definition initF: list val -> itree Es val :=
    fun varg =>
      `sz: Z <- (pargs [Tint] varg)?;;;
      pput (fun (_: Z) => 0%Z);;;
      Ret Vundef
  .

  Definition setF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;;
      data <- pget;;
      pput (fun n => if Z.eq_dec n k then v else data n);;;
      trigger (Syscall "print" (k↑) (fun _ => True));;;
      trigger (Syscall "print" (v↑) (fun _ => True));;;
      Ret Vundef
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;;
      data <- pget;;
      let r := data k in
      trigger (Syscall "print" (k↑) (fun _ => True));;;
      trigger (Syscall "print" (r↑) (fun _ => True));;;
      Ret (Vint r)
  .

  Definition MapSbtb: list (string * fspecbody) :=
    [("init", mk_specbody init_spec (cfunU initF));
     ("set", mk_specbody set_spec (cfunU setF));
     ("get", mk_specbody get_spec (cfunU getF))].

  Definition SMapSem: SModSem.t := {|
    SModSem.fnsems := MapSbtb;
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
End A.
