Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import MutHeader.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  Definition Gsbtb: list (string * fspecbody) := [("g", mk_specbody g_spec (fun _ => trigger (Choose _)))].

  Definition SGSem: SModSem.t := {|
    SModSem.fnsems := Gsbtb;
    SModSem.mn := "G";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition GSem: ModSem.t := (SModSem.to_tgt GlobalStb) SGSem.

  Definition SG: SMod.t := {|
    SMod.get_modsem := fun _ => SGSem;
    SMod.sk := [("g", Sk.Gfun)];
  |}
  .

  Definition G: Mod.t := (SMod.to_tgt GlobalStb) SG.

End PROOF.
