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

  Definition Gsbtb: list (string * fspecbody) := [("g", mk_specbody g_spec (fun _ => trigger (Choose _)))].

  Definition GSem: SModSem.t := {|
    SModSem.fnsems := Gsbtb;
    SModSem.mn := "G";
    SModSem.initial_mr := GRA.embed (IRA.module true: IRA.t);
    SModSem.initial_st := tt↑;
  |}
  .

  Definition G: Mod.t := (SMod.to_tgt (fun _ => GlobalStb)) {|
    SMod.get_modsem := fun _ => GSem;
    SMod.sk := [("g", Sk.Gfun)];
  |}.

End PROOF.
