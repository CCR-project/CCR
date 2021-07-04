Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.
Require Import KnotHeader.
Require Import Invariant.
Require Import STB.

Set Implicit Arguments.




Fixpoint Fib (n: nat): nat :=
  match n with
  | 0 => 1
  | S n' =>
    let r := Fib n' in
    match n' with
    | 0 => 1
    | S n'' => r + Fib n''
    end
  end.

Section MAIN.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Variable RecStb: SkEnv.t -> gname -> option fspec.
  Variable GlobalStb: SkEnv.t -> gname -> option fspec.

  Section SKENV.
    Variable skenv: SkEnv.t.

    Definition fib_spec: fspec :=
      mk_simple (X:=nat*iProp)
                (fun '(n, INV) => (
                     (fun varg o =>
                        ((⌜exists fb,
                               varg = [Vptr fb 0; Vint (Z.of_nat n)]↑ /\ (intrange_64 n) /\ o = ord_pure (2 * n)%nat /\
                               fb_has_spec skenv (RecStb skenv) fb (mrec_spec Fib INV)⌝)
                           ** INV)%I),
                     (fun vret =>
                        (⌜vret = (Vint (Z.of_nat (Fib n)))↑⌝)
                          ** INV)
                )).

    Definition MainFunStb: list (gname * fspec) := [("fib", fib_spec)].

    Definition main_spec:    fspec :=
      mk_simple (X:=(nat -> nat))
                (fun f => (
                     (fun varg o =>
                        (⌜o = ord_top ∧ varg = ([]: list val)↑⌝)
                          ** OwnM (knot_init)
                          ** inv_closed: iProp
                     ),
                     (fun vret =>
                        (⌜vret = (Vint (Z.of_nat (Fib 10)))↑⌝: iProp)%I)
                )).

    Definition MainStb: list (gname * fspec) := [("fib", fib_spec); ("main", main_spec)].

    Definition MainSbtb: list (gname * fspecbody) :=[("fib", mk_specbody fib_spec (fun _ => trigger (Choose _)));
                                                    ("main", mk_specbody main_spec (fun _ => trigger hAPC;;; Ret (Vint (Z.of_nat (Fib 10)))↑))].

    Definition SMainSem: SModSem.t := {|
      SModSem.fnsems := MainSbtb;
      SModSem.mn := "Main";
      SModSem.initial_mr := ε;
      SModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition SMain: SMod.t := {|
    SMod.get_modsem := SMainSem;
    SMod.sk := [("fib", Sk.Gfun)];
  |}
  .

  Definition Main: Mod.t := (SMod.to_tgt GlobalStb) SMain.

End MAIN.
