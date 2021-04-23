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
Require Import KnotHeader.
Require Import STB.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section KNOT.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG knotRA Σ}.

  Variable RecStb: SkEnv.t -> list (gname * fspec).
  Variable FunStb: SkEnv.t -> list (gname * fspec).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Section SKENV.
    Variable skenv: SkEnv.t.

    Definition rec_spec:    fspec := mk_simple (X:=(nat -> nat) * nat)
                                               (fun '(f, n) => (
                                                    (fun varg o => Own (GRA.embed (knot_frag (Some f))) ** ⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n + 1)⌝),
                                                    (fun vret => Own (GRA.embed (knot_frag (Some f))) ** ⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                                               )).

    Definition fun_gen (f: nat -> nat): ftspec (list val) (val) :=
      mk_simple (X:=nat)
                (fun n => (
                     (fun varg o =>
                        (⌜exists fb,
                              varg = [Vptr fb 0; Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n) /\
                              fb_has_spec skenv (RecStb skenv) fb rec_spec⌝)
                          ** Own (GRA.embed (knot_frag (Some f)))),
                     (fun vret =>
                        (⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                          ** Own (GRA.embed (knot_frag (Some f))))
                )).

    Definition KnotRecStb: list (gname * fspec) := [("rec", rec_spec)].

    Definition knot_spec:    fspec :=
      mk_simple (X:=(nat -> nat))
                (fun f => (
                     (fun varg o =>
                        (⌜exists fb,
                              varg = [Vptr fb 0]↑ /\ o = ord_pure 0 /\
                              fb_has_spec skenv (FunStb skenv) fb (fun_gen f)⌝)
                          ** Exists old, Own (GRA.embed (knot_frag old))),
                     (fun vret =>
                        (⌜exists fb,
                            vret = (Vptr fb 0)↑ /\
                            fb_has_spec skenv (RecStb skenv) fb rec_spec⌝)
                          ** Own (GRA.embed (knot_frag (Some f))))
                )).

    Definition KnotStb: list (gname * fspec) := [("rec", rec_spec); ("knot", knot_spec)].

    Definition KnotSbtb: list (gname * fspecbody) :=[("rec", mk_specbody rec_spec (fun _ => trigger (Choose _)));
                                                    ("knot", mk_specbody knot_spec (fun _ => trigger (Choose _)))].

    Definition SKnotSem: SModSem.t := {|
      SModSem.fnsems := KnotSbtb;
      SModSem.mn := "Knot";
      SModSem.initial_mr := GRA.embed (knot_full None);
      SModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition SKnot: SMod.t := {|
    SMod.get_modsem := SKnotSem;
    SMod.sk := [("rec", Sk.Gfun)];
  |}
  .

  Definition Knot: Mod.t := (SMod.to_tgt GlobalStb) SKnot.

End KNOT.
