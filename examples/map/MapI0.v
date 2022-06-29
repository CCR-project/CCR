Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import MapHeader.

Set Implicit Arguments.


(*** module I0 Map
private data: ptr := NULL

def init(sz: int64 ) ≡
  data := calloc(sz)

def set(k: int64, v: int64 ) ≡
  *(data + k) := v
  print("set"+str(k)+str(r))

def get(k: int64): int64 ≡
  var r := *(data + k)
  print("get"+str(k)+str(r))
  return r
***)

Section I0.
  Local Open Scope string_scope.

  Definition initF: list val -> itree Es val :=
    fun varg =>
      `sz: Z <- (pargs [Tint] varg)?;;
      `r: val <- ccallU "alloc" [Vint sz];;
      pput r;;;
      Ret Vundef
  .

  Definition setF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      data <- trigger PGet;; data <- data↓?;; vptr <- (vadd data (Vint k))?;;
      `_: val <- ccallU "store" [vptr; Vint v];;
      trigger (Syscall "print" (k↑) (fun _ => True));;;
      trigger (Syscall "print" (v↑) (fun _ => True));;;
      Ret Vundef
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      data <- trigger PGet;; data <- data↓?;; vptr <- (vadd data (Vint k))?;;
      `r: val <- ccallU "load" [vptr];; r <- (unint r)?;;
      trigger (Syscall "print" (k↑) (fun _ => True));;;
      trigger (Syscall "print" (r↑) (fun _ => True));;;
      Ret (Vint r)
  .

  Definition MapSem: ModSem.t := {|
    ModSem.fnsems := [("init", cfunU initF); ("set", cfunU setF); ("get", cfunU getF)];
    ModSem.mn := "Map";
    ModSem.initial_st := Vnullptr↑;
  |}
  .

  Definition Map: Mod.t := {|
    Mod.get_modsem := fun _ => MapSem;
    Mod.sk := [("init", Sk.Gfun); ("set", Sk.Gfun); ("get", Sk.Gfun)];
  |}
  .
End I0.
