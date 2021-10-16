Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import MWHeader.
Require Import STB.

Set Implicit Arguments.



Section PROOF.

  Context `{@GRA.inG AppRA Σ}.
  Context `{@GRA.inG mwRA Σ}.

  Definition sbtb: list (string * fspecbody) :=
    [("init", mk_specbody init_spec0 (fun _ => trigger (Choose _)));
     ("run", mk_specbody run_spec0 (fun _ => trigger (Choose _)))].

  Definition SAppSem: SModSem.t := {|
    SModSem.fnsems := sbtb;
    SModSem.mn := "App";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SApp: SMod.t := {|
    SMod.get_modsem := fun _ => SAppSem;
    SMod.sk := [("init", Sk.Gfun); ("run", Sk.Gfun)];
  |}
  .

  Definition App: Mod.t := (SMod.to_tgt (fun _ => GlobalStb1)) SApp.

End PROOF.