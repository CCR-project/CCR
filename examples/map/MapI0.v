Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import MapHeader.

Set Implicit Arguments.


(*** module I Map
private data := NULL

def init(sz: int) ≡
  data := calloc(sz)

def get(k: int): int ≡
  return *(data + k)

def set(k: int, v: int) ≡
  *(data + k) := v

def set_by_user(k: int) ≡
  set(k, input())
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

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      data <- trigger PGet;; data <- data↓?;; vptr <- (vadd data (Vint k))?;;
      `r: val <- ccallU "load" [vptr];; r <- (unint r)?;;
      Ret (Vint r)
  .

  Definition setF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      data <- trigger PGet;; data <- data↓?;; vptr <- (vadd data (Vint k))?;;
      `_: val <- ccallU "store" [vptr; Vint v];;
      Ret Vundef
  .

  Definition set_by_userF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      v <- trigger (Syscall "input" (([]: list Z)↑) (fun _ => True));; v <- v↓?;;
      ccallU "set" [Vint v]
  .

  Definition MapSem: ModSem.t := {|
    ModSem.fnsems := [("init", cfunU initF); ("get", cfunU getF); ("set", cfunU setF); ("set_by_user", cfunU set_by_userF)];
    ModSem.mn := "Map";
    ModSem.initial_st := Vnullptr↑;
  |}
  .

  Definition Map: Mod.t := {|
    Mod.get_modsem := fun _ => MapSem;
    Mod.sk := [("init", Sk.Gfun); ("get", Sk.Gfun); ("set", Sk.Gfun); ("set_by_user", Sk.Gfun)];
  |}
  .
End I0.
