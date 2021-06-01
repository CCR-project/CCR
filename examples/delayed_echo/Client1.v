Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef Logic.
Require Import Client0.
Require Import TODOYJ.

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.

  Let getint_spec: fspec := (mk_simple (X:=unit) (fun _ => ((fun _ o => (⌜o = ord_top⌝: iProp)%I), top2))).
  Let putint_spec: fspec := (mk_simple (X:=unit) (fun _ => ((fun _ o => (⌜o = ord_top⌝: iProp)%I), top2))).

  Definition ClientStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("getint", getint_spec) ; ("putint", putint_spec)].
  Defined.

  Definition getint_body: list val -> itree (hCallE +' pE +' eventE) val := resum_ktr getintF.
  Definition putint_body: list val -> itree (hCallE +' pE +' eventE) val := resum_ktr putintF.

  Definition ClientSbtb: list (gname * fspecbody) :=
    [("getint", mk_specbody getint_spec (cfun getint_body)); ("putint", mk_specbody putint_spec (cfun putint_body))]
  .

  Definition SClientSem: SModSem.t := {|
    SModSem.fnsems := ClientSbtb;
    SModSem.mn := "Client";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition ClientSem: ModSem.t := (SModSem.to_tgt ClientStb) SClientSem.

  Definition SClient: SMod.t := {|
    SMod.get_modsem := fun _ => SClientSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition Client: Mod.t := (SMod.to_tgt (fun _ => ClientStb)) SClient.

End PROOF.
Global Hint Unfold ClientStb: stb.
