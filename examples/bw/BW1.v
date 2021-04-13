Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Stack1 Client1.
Require Import TODOYJ.
Require Import Logic.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Definition bwRA: URA.t := Auth.t (Excl.t bool).
Definition bw_full (b: bool) : (@URA.car bwRA) := Auth.black (M:=(Excl.t _)) (Some b).
Definition bw_frag (b: bool) : (@URA.car bwRA) := Auth.white (M:=(Excl.t _)) (Some b).

Section BW.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG bwRA Σ}.

  Let get_spec:  fspec := (mk_simple "BW"
                                     (fun b => (
                                          (fun varg o => (Own (GRA.embed (bw_frag b)) ** ⌜o = ord_pure 1⌝)),
                                          (fun vret => (Own (GRA.embed (bw_frag b)) ** ⌜vret = (Vint (if b then 0xffffff else 0))↑⌝))
                                        ))).

  Let flip_spec: fspec := (mk_simple "BW"
                                     (fun b => (
                                          (fun varg o => (Own (GRA.embed (bw_frag b)) ** ⌜o = ord_pure 1⌝)),
                                          (fun vret => (Own (GRA.embed (bw_frag (negb b)))))
                                        ))).

  Definition BWStb: list (gname * fspec) :=
    Seal.sealing "stb" [("get", get_spec) ; ("flip", flip_spec)].

  Definition BWSbtb: list (gname * fspecbody) :=
    [("get", mk_specbody get_spec (fun _ => APC;; trigger (Choose _)));
    ("flip", mk_specbody flip_spec (fun _ => APC;; trigger (Choose _)))
    ]
  .

  Definition BWSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt BWStb fn fsb)) BWSbtb;
    ModSem.mn := "BW";
    ModSem.initial_mr := GRA.embed (bw_full false);
    ModSem.initial_st := tt↑;
  |}
  .

  Definition BW: Mod.t := {|
    Mod.get_modsem := fun _ => BWSem;
    Mod.sk := Sk.unit;
  |}
  .

End BW.
Global Hint Unfold BWStb: bw.
