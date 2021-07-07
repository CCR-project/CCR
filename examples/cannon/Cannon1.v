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
Require Import CannonRA Cannon0.

Set Implicit Arguments.



Section CANNON.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG CannonRA Σ}.

  Definition fire_spec:    fspec :=
    mk_simple (X:=unit)
              (fun _ => (
                   (fun varg o =>
                      (⌜varg = ([]: list val)↑ /\ o = ord_top⌝)
                        ** (OwnM (Ball))
                   ),
                   (fun vret =>
                      (⌜vret = (1: Z)%Z↑⌝)%I
                   )
              )).

  Definition CannonSbtb: list (gname * fspecbody) :=
    [("fire", mk_specbody fire_spec (cfunN fire_body))].

  Definition SCannonSem: SModSem.t := {|
    SModSem.fnsems := CannonSbtb;
    SModSem.mn := "Cannon";
    SModSem.initial_mr := GRA.embed Ready;
    SModSem.initial_st := (1: Z)%Z↑;
  |}
  .

  Definition SCannon: SMod.t := {|
    SMod.get_modsem := fun _ => SCannonSem;
    SMod.sk := [("fire", Sk.Gfun)];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Cannon: Mod.t := (SMod.to_tgt GlobalStb) SCannon.
End CANNON.
