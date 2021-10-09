Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import IntroHeader.
Import Plain.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG IRA.t Σ}.

  Definition Fsbtb: list (string * fspecbody) := [("f", mk_specbody f_spec (fun _ => trigger (Choose _)))].

  Definition FSem: SModSem.t := {|
    SModSem.fnsems := Fsbtb;
    SModSem.mn := "F";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition F: Mod.t := (SMod.to_tgt (fun _ => GlobalStb)) {|
    SMod.get_modsem := fun _ => FSem;
    SMod.sk := [("f", Sk.Gfun)];
  |}.

End PROOF.
