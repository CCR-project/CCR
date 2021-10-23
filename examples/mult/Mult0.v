Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import MultHeader.

Set Implicit Arguments.



Section PROOF.
  Context `{@GRA.inG multRA Σ}.

  Definition multSbtb: list (gname * fspecbody) :=
    [("fire", mk_specbody f_spec (fun _ => Ret Vundef↑))].

  Definition SMultSem: SModSem.t := {|
    SModSem.fnsems := multSbtb;
    SModSem.mn := "Mult";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SMult: SMod.t := {|
    SMod.get_modsem := fun _ => SMultSem;
    SMod.sk := [];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Mult: Mod.t := (SMod.to_tgt GlobalStb) SMult.
End PROOF.

