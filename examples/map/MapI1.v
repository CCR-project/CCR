Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import MapHeader.

Set Implicit Arguments.


(*** module I1 Map
TODO
***)

Section I1.
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
      trigger (Syscall "print" (k↑) (fun _ => True));;;
      trigger (Syscall "print" (v↑) (fun _ => True));;;
      Ret Vundef
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      data <- trigger PGet;; data <- data↓?;; data <- (unint data)?;;
      `r: val <- ccallU "load" [Vint (data + k)];; r <- (unint r)?;;
      trigger (Syscall "print" (k↑) (fun _ => True));;;
      trigger (Syscall "print" (r↑) (fun _ => True));;;
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
End I1.
