Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Mem1.
Require Import TODOYJ.
Require Import Logic YPM.
Require Import KnotHeader.
Require Import STB.

Set Implicit Arguments.



Section KNOT.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Variable RecStb: SkEnv.t -> list (gname * fspec).
  Variable FunStb: SkEnv.t -> list (gname * fspec).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Section SKENV.
    Variable skenv: SkEnv.t.

    Definition rec_spec:    fspec :=
      mk_inv_simple (X:=(nat -> nat) * nat)
                    (fun '(f, n) => (
                         (fun varg o =>
                            (⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n + 1)%nat⌝)
                              ** (OwnM (knot_frag (Some f)))
                         ),
                         (fun vret =>
                            (⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                              ** (Own (GRA.embed (knot_frag (Some f))))
                         )
                    )).

    Definition fun_gen (f: nat -> nat): ftspec (list val) (val) :=
      mk_inv_simple (X:=nat)
                    (fun n => (
                         (fun varg o =>
                            (⌜exists fb,
                                  varg = [Vptr fb 0; Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n)%nat /\
                                  fb_has_spec skenv (RecStb skenv) fb rec_spec⌝)
                              ** OwnM (knot_frag (Some f))
                         ),
                         (fun vret =>
                            (⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                              ** OwnM (knot_frag (Some f))
                         )
                    )).

    Definition KnotRecStb: list (gname * fspec) := [("rec", rec_spec)].

    Definition knot_spec:    fspec :=
      mk_inv_simple (X:=(nat -> nat))
                    (fun f => (
                         (fun varg o =>
                            (⌜exists fb,
                                  varg = [Vptr fb 0]↑ /\ o = ord_pure 1 /\
                                  fb_has_spec skenv (FunStb skenv) fb (fun_gen f)⌝)
                              ** (∃ old, OwnM (knot_frag old))
                         ),
                         (fun vret =>
                            (⌜exists fb,
                                  vret = (Vptr fb 0)↑ /\
                                  fb_has_spec skenv (RecStb skenv) fb rec_spec⌝)
                              ** OwnM (knot_frag (Some f))
                         )
                    )).

    Definition knot_spec2:    fspec :=
      mk_simple (X:=(nat -> nat))
                (fun f => (
                     (fun varg o =>
                        (⌜exists fb,
                              varg = [Vptr fb 0]↑ /\ o = ord_pure 1 /\
                              fb_has_spec skenv (FunStb skenv) fb (fun_gen f)⌝)
                          ** OwnM (knot_init)
                          ** inv_opener
                     ),
                     (fun vret =>
                        (∃ INV,
                            (⌜exists fb,
                                  vret = (Vptr fb 0)↑ /\
                                  fb_has_spec skenv (RecStb skenv) fb (mrec_spec f INV)⌝)
                              ** INV)%I
                     )
                )).

    Definition KnotStb: list (gname * fspec) := [("rec", rec_spec); ("knot", knot_spec)].

    Definition KnotSbtb: list (gname * fspecbody) :=[("rec", mk_specbody rec_spec (fun _ => trigger (Choose _)));
                                                    ("knot", mk_specbody knot_spec (fun _ => trigger (Choose _)))].

    Definition SKnotSem: SModSem.t := {|
      SModSem.fnsems := KnotSbtb;
      SModSem.mn := "Knot";
      SModSem.initial_mr := (GRA.embed (inv_black tt↑ tt ↑)) ⋅ (GRA.embed (var_points_to skenv "_f" Vundef)) ⋅ (GRA.embed (knot_full None)) ;
      SModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition SKnot: SMod.t := {|
    SMod.get_modsem := SKnotSem;
    SMod.sk := [("rec", Sk.Gfun); ("_f", Sk.Gvar Vundef)];
  |}
  .

  Definition Knot: Mod.t := (SMod.to_tgt GlobalStb) SKnot.
End KNOT.


Section WEAK.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Lemma rec_spec_weaker f: ftspec_weaker (mrec_spec f (OwnM (knot_frag (Some f)) ** inv_opener)) rec_spec.
  Proof.
    ii. ss. exists (f, x_src). split.
    { intros arg_src arg_tgt o. ss.
      iIntros "[[H0 [H1 H2]] H3]". iModIntro. iFrame. }
    { intros ret_src ret_tgt. ss.
      iIntros "[[H0 [H1 H2]] H3]". iModIntro. iFrame. }
  Qed.
End WEAK.

Section WEAK.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Variable RecStb: SkEnv.t -> list (gname * fspec).
  Variable FunStb: SkEnv.t -> list (gname * fspec).

  Lemma knot_spec2_weaker skenv: ftspec_weaker (knot_spec2 RecStb FunStb skenv) (knot_spec RecStb FunStb skenv).
  Proof.
    ii. ss. exists x_src. split.
    { intros arg_src arg_tgt o.
      iIntros "[[[H0 H1] H2] H3]". iModIntro.
      iFrame. iExists (None: option (nat -> nat)). ss. }
    { intros ret_src ret_tgt.
      iIntros "[[H0 [H1 H2]] H3]". iModIntro. iFrame.
      iExists (OwnM (knot_frag (Some x_src)) ** inv_opener).
      iFrame. iDestruct "H1" as "%". iPureIntro. des. eexists.
      split; eauto. eapply fb_has_spec_weaker; eauto.
      eapply rec_spec_weaker.
    }
  Qed.
End WEAK.
