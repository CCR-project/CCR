Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Stack1.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.






Section BW.

  Context `{Σ: GRA.t}.

(***
local numFlip = 0

def get(): Int
  r = (numFlip &2 == 0) ? 0 : 1
  return r

def flip(): Unit
  numFlip := numFlip+1
  return ()
***)

  Definition getF: list val -> itree Es val :=
    fun _ =>
      n <- trigger (PGet "BW");; `n: Z <- n↓?;;
      let r := (if (Z.even n) then Vint 0 else Vint (0xffffff)) in
      Ret r
    .

  Definition flipF: list val -> itree Es val :=
    fun _ =>
      n <- trigger (PGet "BW");; `n: Z <- n↓?;;
      let n := (n+1)%Z in
      trigger (PPut "BW" n↑);;
      Ret Vundef
    .

  Definition BWSem: ModSem.t := {|
    ModSem.fnsems := [("get", cfun getF); ("flip", cfun flipF)];
    ModSem.initial_mrs := [("BW", (ε, 0%Z↑))];
  |}
  .

  Definition BW: Mod.t := {|
    Mod.get_modsem := fun _ => BWSem;
    Mod.sk := Sk.unit;
  |}
  .
End BW.
