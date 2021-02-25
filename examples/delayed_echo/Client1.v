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

  Let in_spec:  fspec := (mk_simple "Client" (X:=unit) (fun _ _ o _ => o = ord_top) (top3)).
  Let out_spec: fspec := (mk_simple "Client" (X:=unit) (fun _ _ o _ => o = ord_top) (top3)).

  Definition ClientStb: list (gname * fspec) :=
    [("in", in_spec) ; ("out", out_spec)]
  .

  Definition in_body:  list val -> itree (hCallE +' pE +' eventE) val := resum_ktr inF.
  Definition out_body: list val -> itree (hCallE +' pE +' eventE) val := resum_ktr inF.

  Definition ClientSbtb: list (gname * fspecbody) :=
    [("in", mk_specbody in_spec in_body); ("out", mk_specbody out_spec out_body)]
  .

  Definition ClientSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt ClientStb fn fsb)) ClientSbtb;
    ModSem.initial_mrs := [("Client", (ε, tt↑))];
  |}
  .

  Definition Client: Mod.t := {|
    Mod.get_modsem := fun _ => ClientSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
