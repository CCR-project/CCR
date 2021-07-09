Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef OpenDef.

Set Implicit Arguments.






Section PROOF.

  Context `{Σ: GRA.t}.

  Definition main_body: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;;
      `_:val <- (ccallN "echo" ([]: list val));;;
      Ret (Vint 0)
  .

  Definition MainSem: KModSem.t := {|
    KModSem.fnsems := [("main", ksb_trivial (cfunN main_body))];
    KModSem.mn := "main";
    KModSem.initial_mr := ε;
    KModSem.initial_st := tt↑;
  |}
  .

  Definition Main: KMod.t := {|
    KMod.get_modsem := fun _ => MainSem;
    KMod.sk := Sk.unit;
  |}
  .
End PROOF.
