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

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Definition knotRA: URA.t := Auth.t (Excl.t (nat -> nat)).
Definition knot_full (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.black (M:=(Excl.t _)) f.
Definition knot_frag (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.white (M:=(Excl.t _)) f.



Section KNOT.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG knotRA Σ}.

  Variable RecStb: SkEnv.t -> list (gname * fspec).
  Variable FunStb: SkEnv.t -> list (gname * fspec).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Section SKENV.
    Variable skenv: SkEnv.t.

    Definition rec_spec:    fspec := mk_simple "Knot" (X:=(nat -> nat) * nat)
                                               (fun '(f, n) => (
                                                    (fun varg o => Own (GRA.embed (knot_frag (Some f))) ** ⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n - 1)⌝),
                                                    (fun vret => ⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                                               )).

    Definition KnotRecStb: list (gname * fspec) := [("rec", rec_spec)].

    Definition fun_gen (f: nat -> nat) (mn: mname): fspec :=
      mk_simple mn (X:=nat)
                (fun n => (
                     (fun varg o =>
                        ⌜exists fb fn,
                            varg = [Vptr fb 0; Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n) /\
                            skenv.(SkEnv.blk2id) fb = Some fn /\
                            List.find (fun '(_fn, _) => dec fn _fn) (RecStb skenv) = Some (fn, rec_spec)⌝ ** Own (GRA.embed (knot_frag (Some f)))),
                     (fun vret => ⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                )).

    Definition knot_spec:    fspec :=
      mk_simple "Knot" (X:=(nat -> nat))
                (fun f => (
                     (fun varg o =>
                        ⌜exists fn fb,
                            varg = [Vptr fb 0]↑ /\ o = ord_pure 0 /\
                            skenv.(SkEnv.blk2id) fb = Some fn /\
                            List.find (fun '(_fn, _) => dec fn _fn) (FunStb skenv) = Some (fn, fun_gen f fn)⌝ ** Exists old, Own (GRA.embed (knot_frag old))),
                     (fun vret => ⌜exists fn fb,
                            vret = (Vptr fb 0)↑ /\
                            skenv.(SkEnv.blk2id) fb = Some fn /\
                            List.find (fun '(_fn, _) => dec fn _fn) (RecStb skenv) = Some (fn, rec_spec)⌝ ** Own (GRA.embed (knot_frag (Some f))))
                )).

    Definition KnotStb: list (gname * fspec) := [("rec", rec_spec); ("knot", knot_spec)].

    Definition KnotSbtb: list (gname * fspecbody) :=[("rec", mk_specbody rec_spec (fun _ => trigger (Choose _)));
                                                    ("knot", mk_specbody knot_spec (fun _ => trigger (Choose _)))].

    Definition KnotSem: ModSem.t := {|
      ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt (GlobalStb skenv) fn body)) KnotSbtb;
      ModSem.mn := "Knot";
      ModSem.initial_mr := ε;
      ModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition Knot: Mod.t := {|
    Mod.get_modsem := fun skenv => KnotSem skenv;
    Mod.sk := [("rec", Sk.Gfun)];
  |}
  .

End KNOT.
