Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import IntroHeader.

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
      ccallU "malloc" [Vint sz]
  .

  Definition setF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      data <- trigger PGet;; data <- data↓?;; data <- (unint data)?;;
      `_: val <- ccallU "store" [Vint (data + k); Vint v];;
      ccallU "print" ("set" ++ Z_to_string k ++ Z_to_string v)
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      data <- trigger PGet;; data <- data↓?;; data <- (unint data)?;;
      `r: val <- ccallU "load" [Vint (data + k)];; r <- (unint r)?;;
      `_: val <- ccallU "print" ("get" ++ Z_to_string k ++ Z_to_string r);;
      Ret (Vint r)
  .

  Definition I0Sem: ModSem.t := {|
    ModSem.fnsems := [("init", cfunU initF); ("set", cfunU setF); ("get", cfunU getF)];
    ModSem.mn := "Map";
    ModSem.initial_st := Vnullptr↑;
  |}
  .

  Definition I0: Mod.t := {|
    Mod.get_modsem := fun _ => I0Sem;
    Mod.sk := [];
  |}
  .
End I0.
