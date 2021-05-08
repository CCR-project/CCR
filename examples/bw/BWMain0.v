Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import BW1.
Require Import TODOYJ.

Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODO TODOYJ.

Set Implicit Arguments.






Section BW.

  Context `{Σ: GRA.t}.

(***
def main(): Unit
  b = CL.getbool();
  if (b) { BW.flip() }
  i = BW.get()
  CL.putint(i)
  return()
***)

  Definition mainF: list val -> itree Es val :=
    fun _ =>
      `b: val <- ccall "getbool" ([]: list val);; `b: bool <- (unbool b)?;;
      (if(b)
       then ccall "flip" ([]: list val)
       else Ret Vundef);;;
      `i: val <- ccall "get" ([]: list val);;
      `_: val <- ccall "putint" [i];;
      Ret Vundef
  .

  Definition MainSem: ModSem.t := {|
    ModSem.fnsems := [("main", cfun mainF)];
    ModSem.mn := "Main";
    ModSem.initial_mr := ε;
    ModSem.initial_st := 0%Z↑;
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := Sk.unit;
  |}
  .
End BW.
