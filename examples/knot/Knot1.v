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

Generalizable Variables E R A B C X Y Σ.

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
      mk_simple (X:=(nat -> nat) * nat)
                (fun '(f, n) => (
                     (fun varg o =>
                        (⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n + 1)⌝)
                          ** (Own (GRA.embed (knot_frag (Some f))))
                          ** inv_closed
                     ),
                     (fun vret =>
                        (⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                          ** (Own (GRA.embed (knot_frag (Some f))))
                          ** inv_closed
                     )
                )).

    Definition fun_gen (f: nat -> nat): ftspec (list val) (val) :=
      mk_simple (X:=nat)
                (fun n => (
                     (fun varg o =>
                        (⌜exists fb,
                              varg = [Vptr fb 0; Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n) /\
                              fb_has_spec skenv (RecStb skenv) fb rec_spec⌝)
                          ** Own (GRA.embed (knot_frag (Some f)))
                          ** inv_closed
                     ),
                     (fun vret =>
                        (⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                          ** Own (GRA.embed (knot_frag (Some f)))
                          ** inv_closed
                     )
                )).

    Definition KnotRecStb: list (gname * fspec) := [("rec", rec_spec)].

    Definition knot_spec:    fspec :=
      mk_simple (X:=(nat -> nat))
                (fun f => (
                     (fun varg o =>
                        (⌜exists fb,
                              varg = [Vptr fb 0]↑ /\ o = ord_pure 1 /\
                              fb_has_spec skenv (FunStb skenv) fb (fun_gen f)⌝)
                          ** (Exists old, Own (GRA.embed (knot_frag old)))
                          ** inv_closed
                     ),
                     (fun vret =>
                        (⌜exists fb,
                              vret = (Vptr fb 0)↑ /\
                              fb_has_spec skenv (RecStb skenv) fb rec_spec⌝)
                          ** Own (GRA.embed (knot_frag (Some f)))
                          ** inv_closed
                     )
                )).

    Definition knot_spec2:    fspec :=
      mk_simple (X:=(nat -> nat))
                (fun f => (
                     (fun varg o =>
                        (⌜exists fb,
                              varg = [Vptr fb 0]↑ /\ o = ord_pure 1 /\
                              fb_has_spec skenv (FunStb skenv) fb (fun_gen f)⌝)
                          ** Own (GRA.embed knot_init)
                          ** inv_closed
                     ),
                     (fun vret =>
                        Exists INV,
                        (⌜exists fb,
                              vret = (Vptr fb 0)↑ /\
                              fb_has_spec skenv (RecStb skenv) fb (mrec_spec f INV)⌝)
                          ** INV
                     )
                )).

    Definition KnotStb: list (gname * fspec) := [("rec", rec_spec); ("knot", knot_spec)].

    Definition KnotSbtb: list (gname * fspecbody) :=[("rec", mk_specbody rec_spec (fun _ => trigger (Choose _)));
                                                    ("knot", mk_specbody knot_spec (fun _ => trigger (Choose _)))].

    Definition knot_var (v: val): Σ :=
      match (skenv.(SkEnv.id2blk) "_f") with
      | Some  blk => GRA.embed ((blk,0%Z) |-> [v])
      | None => ε
      end.

    Definition SKnotSem: SModSem.t := {|
      SModSem.fnsems := KnotSbtb;
      SModSem.mn := "Knot";
      SModSem.initial_mr := knot_var Vundef ⋅ (GRA.embed (knot_full None)) ⋅ (GRA.embed inv_black);
      SModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition SKnot: SMod.t := {|
    SMod.get_modsem := SKnotSem;
    SMod.sk := [("rec", Sk.Gfun); ("_f", Sk.Gvar 0)];
  |}
  .

  Definition Knot: Mod.t := (SMod.to_tgt GlobalStb) SKnot.
End KNOT.


Section WEAK.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Lemma rec_spec_weaker f: ftspec_weaker (mrec_spec f (Own (GRA.embed (knot_frag (Some f))) ** inv_closed)) rec_spec.
  Proof.
    ii. ss. exists (f, x_src). split.
    { intros arg_src arg_tgt o. ss. iIntro. (* TODO: use iIntros *)
      iDestruct A; subst. iSplitP; ss.
      iDestruct A. iDestruct A0. iSplitR A1; ss. iSplitR A0; ss. (* TODO: make lemma: ** is commute *) }
    { intros ret_src ret_tgt. ss. iIntro. (* TODO: use iIntros *)
      iDestruct A; subst. iSplitP; ss.
      iDestruct A. iDestruct A. iSplitL A; ss. iSplitR A0; ss. (* TODO: make lemma: ** is commute *) }
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
    { intros arg_src arg_tgt o. iIntro. iDestruct A; subst. iSplitP; ss.
      iRefresh. iDestruct A. iSplitL A.
      { iDestruct A. iSplitL A; ss.
        iExists (None: option (nat -> nat)). ss. }
      { iApply A0. }
    }
    { intros ret_src ret_tgt. iIntro. iDestruct A; subst. iSplitP; ss.
      iRefresh. iDestruct A.
      iExists (Own (GRA.embed (knot_frag (Some x_src))) ** inv_closed).
      iDestruct A. iMerge A1 A0. iSplitR A1; ss.
      iPure A. des. iExists fb. split; auto.
      eapply fb_has_spec_weaker; eauto.
      eapply rec_spec_weaker.
    }
  Qed.
End WEAK.
