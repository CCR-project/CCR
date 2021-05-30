Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.

Set Implicit Arguments.



Definition bwRA: URA.t := Auth.t (Excl.t bool).
Definition bw_full (b: bool) : (@URA.car bwRA) := Auth.black (M:=(Excl.t _)) (Some b).
Definition bw_frag (b: bool) : (@URA.car bwRA) := Auth.white (M:=(Excl.t _)) (Some b).

Section BW.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG bwRA Σ}.

  Let get_spec:  fspec := (mk_simple (fun b => (
                                          (fun varg o => (OwnM (bw_frag b)) ** ⌜o = ord_pure 1⌝),
                                          (fun vret => (OwnM (bw_frag b)) ** ⌜vret = (Vint (if b then 0xffffff%Z else 0))↑⌝)
                          ))).

  Let flip_spec: fspec := (mk_simple (fun b => (
                                          (fun varg o => (OwnM (bw_frag b) ** ⌜o = ord_pure 1⌝)),
                                          (fun vret => (OwnM (bw_frag (negb b))))
                          ))).

  Definition BWStb: list (gname * fspec) :=
    Seal.sealing "stb" [("get", get_spec) ; ("flip", flip_spec)].

  Definition BWSbtb: list (gname * fspecbody) :=
    [("get", mk_specbody get_spec (fun _ => APC;;; trigger (Choose _)));
    ("flip", mk_specbody flip_spec (fun _ => APC;;; trigger (Choose _)))
    ]
  .

  Definition SBWSem: SModSem.t := {|
    SModSem.fnsems := BWSbtb;
    SModSem.mn := "BW";
    SModSem.initial_mr := GRA.embed (bw_full false);
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SBW: SMod.t := {|
    SMod.get_modsem := fun _ => SBWSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition BWSem: ModSem.t := SModSem.to_tgt BWStb SBWSem.

  Definition BW: Mod.t := SMod.to_tgt (fun _ => BWStb) SBW.

End BW.
Global Hint Unfold BWStb: stb.
