Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import Mem1.
Require Import AList.
Require Import MWHeader.

Set Implicit Arguments.



Definition _stkRA: URA.t := (mblock ==> (Excl.t (list val)))%ra.
Instance stkRA: URA.t := Auth.t _stkRA.

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG mapRA Σ}.
  Context `{@GRA.inG memRA Σ}.

  (* Lemma unfold_is_map_internal: forall ll xs, *)
  (*     is_map_internal ll xs = *)
  (*     match xs with *)
  (*     | [] => (⌜ll = Vnullptr⌝: iProp)%I *)
  (*     | xhd :: xtl => *)
  (*       (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                              ** is_map_internal ltl xtl: iProp)%I *)
  (*     end *)
  (* . *)
  (* Proof. *)
  (*   i. destruct xs; auto. *)
  (* Qed. *)

  (* Lemma unfold_is_map_internal_cons: forall ll xhd xtl, *)
  (*     is_map_internal ll (xhd :: xtl) = *)
  (*     (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                            ** is_map_internal ltl xtl: iProp)%I. *)
  (* Proof. *)
  (*   i. eapply unfold_is_map_internal. *)
  (* Qed. *)


  Definition MapSbtb: list (gname * fspecbody) :=
    [("Map.new", mk_specbody new_spec (fun _ => triggerNB));
    ("Map.update", mk_specbody update_spec (fun _ => triggerNB));
    ("Map.access", mk_specbody access_spec (fun _ => triggerNB));
    ("Map.loop", mk_specbody access_loop_spec (fun _ => triggerNB))
    ]
  .

  Definition MapStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun fsb => fsb.(fsb_fspec): fspec)) MapSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition SMapSem: SModSem.t := {|
    SModSem.fnsems := MapSbtb;
    SModSem.mn := "Map";
    SModSem.initial_mr := GRA.embed (@Auth.black _mapRA ε);
    SModSem.initial_st := (* (∅: gmap mblock (list val)) *)tt↑;
  |}
  .

  Definition SMap: SMod.t := {|
    SMod.get_modsem := fun _ => SMapSem;
    SMod.sk := [("Map.new", Sk.Gfun); ("Map.update", Sk.Gfun); ("Map.access", Sk.Gfun); ("Map.loop", Sk.Gfun)];
  |}
  .

  Definition Map (stb: Sk.t -> gname -> option fspec): Mod.t :=
    SMod.to_tgt stb SMap.

End PROOF.
Global Hint Unfold MapStb: stb.
