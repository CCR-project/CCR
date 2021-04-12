Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Client0.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.

  Let getint_spec:  fspec := (mk_simple "Client" (X:=unit) (fun _ _ o _ => o = ord_top) (top3)).
  Let putint_spec: fspec := (mk_simple "Client" (X:=unit) (fun _ _ o _ => o = ord_top) (top3)).

  Definition ClientStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("getint", getint_spec) ; ("putint", putint_spec)].
  Defined.

  Definition getint_body: list val -> itree (hCallE +' pE +' eventE) val := resum_ktr getintF.
  Definition putint_body: list val -> itree (hCallE +' pE +' eventE) val := resum_ktr putintF.

  Definition ClientSbtb: list (gname * fspecbody) :=
    [("in", mk_specbody getint_spec getint_body); ("putint", mk_specbody putint_spec putint_body)]
  .

  Definition ClientSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt ClientStb fn fsb)) ClientSbtb;
    ModSem.mn := "Client";
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Client: Mod.t := {|
    Mod.get_modsem := fun _ => ClientSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
Global Hint Unfold ClientStb: stb.
