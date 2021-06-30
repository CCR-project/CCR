Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.
(* Require Import Mem0 MemOpen. *)
Require Import HoareDef.
Require Import Red IRed.

Set Implicit Arguments.



(*** TODO: remove redundancy ***)
Ltac my_red_both := try (prw _red_gen 2 0); try (prw _red_gen 1 0).

(*** TODO: move to TODOYJ ***)
Definition my_if X (b: bool) (x0 x1: X): X := if b then x0 else x1.
Lemma my_if_same: forall X b (x: X), my_if b x x = x. i. destruct b; ss. Qed.



(********************************************* KNOWN ***********************************************)
(********************************************* KNOWN ***********************************************)
(********************************************* KNOWN ***********************************************)

Section AUX.
  Context `{Σ: GRA.t}.

  Variant kflag: Type := (** known and **) pure | (** known and **) impure.

  Variant kCallE: Type -> Type :=
  | kCall (kf: kflag) (fn: gname) (varg: Any.t): kCallE Any.t
  .

  Definition kcall {X Y} (kf: kflag) (fn: gname) (varg: X): itree (kCallE +' pE +' eventE) Y :=
    vret <- trigger (kCall kf fn varg↑);; vret <- vret↓ǃ;; Ret vret.

  Record kspecbody := mk_kspecbody {
    ksb_fspec:> fspec;                                            (*** K -> K ***)
    ksb_ubody: (option mname * Any.t) -> itree (kCallE +' pE +' eventE) Any.t;     (*** U -> K ***)
    ksb_kbody: (option mname * Any.t) -> itree (kCallE +' pE +' eventE) Any.t;     (*** K -> K ***)
  }
  .

  Definition ksb_trivial (body: (option mname * Any.t) -> itree (kCallE +' pE +' eventE) Any.t): kspecbody :=
    mk_kspecbody fspec_trivial body body
  .

  Program Fixpoint _APCK (at_most: Ord.t) {wf Ord.lt at_most}: itree (kCallE +' pE +' eventE) unit :=
    break <- trigger (Choose _);;
    if break: bool
    then Ret tt
    else
      n <- trigger (Choose Ord.t);;
      trigger (Choose (n < at_most)%ord);;;
      '(fn, varg) <- trigger (Choose _);;
      trigger (kCall pure fn varg);;;
      _APCK n.
  Next Obligation. ss. Qed.
  Next Obligation. eapply Ord.lt_well_founded. Qed.

  Definition APCK: itree (kCallE +' pE +' eventE) unit :=
    at_most <- trigger (Choose _);;
    guarantee(at_most < kappa)%ord;;;
    _APCK at_most
  .

  Lemma unfold_APCK:
    forall at_most, _APCK at_most =
                    break <- trigger (Choose _);;
                    if break: bool
                    then Ret tt
                    else
                      n <- trigger (Choose Ord.t);;
                      guarantee (n < at_most)%ord;;;
                      '(fn, varg) <- trigger (Choose _);;
                      trigger (kCall pure fn varg);;;
                      _APCK n.
  Proof.
    i. unfold _APCK. rewrite Fix_eq; eauto.
    { repeat f_equal. extensionality break. destruct break; ss.
      repeat f_equal. extensionality n.
      unfold guarantee. rewrite bind_bind.
      repeat f_equal. extensionality p.
      rewrite bind_ret_l.
      repeat f_equal. extensionality x. des_ifs. }
    { i. replace g with f; auto. extensionality o. eapply H. }
  Qed.
  Global Opaque _APCK.

End AUX.


(* TODO: move it to somewhere *)
Global Program Instance option_Dec A `{Dec A}: Dec (option A).
Next Obligation.
Proof.
  i. destruct a0, a1.
  - destruct (H a a0).
    + left. f_equal. apply e.
    + right. ii. inversion H0. et.
  - right. ss.
  - right. ss.
  - left. refl.
Defined.

Module KModSem.
Section KMODSEM.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    (* fnsems: list (gname * (list val -> itree (oCallE +' pE +' eventE) val)); *)
    fnsems: list (gname * kspecbody);
    mn: mname;
    initial_mr: Σ;
    initial_st: Any.t;
  }
  .

  (************************* TGT ***************************)
  (************************* TGT ***************************)
  (************************* TGT ***************************)

  Definition transl_kCallE_tgt: kCallE ~> hCallE :=
    fun _ '(kCall kf fn args) =>
      match kf with
      | pure => hCall true fn (Any.pair true↑ args)
      | impure => hCall false fn (Any.pair true↑ args)
      end
  .

  Definition transl_event_tgt: (kCallE +' pE +' eventE) ~> (hCallE +' pE +' eventE) :=
    (bimap transl_kCallE_tgt (bimap (id_ _) (id_ _)))
  .

  Definition transl_itr_tgt: itree (kCallE +' pE +' eventE) ~> itree (hCallE +' pE +' eventE) :=
    fun _ => interp (T:=_) (fun _ e => trigger (transl_event_tgt e))
  .

  Definition transl_fun_tgt (ktr: (option mname * Any.t) -> itree (kCallE +' pE +' eventE) Any.t):
    (option mname * Any.t) -> itree (hCallE +' pE +' eventE) Any.t :=
    (transl_itr_tgt (T:=_)) ∘ ktr
  .

  Definition disclose_tgt (fs: fspec): fspec :=
    mk_fspec (meta:=option fs.(meta))
             (fun mn ox argh argl o =>
                match ox with
                | Some x => (∃ argh', ⌜argh = Any.pair true↑ argh'⌝ ∧ (fs.(precond) mn x argh' argl o: iProp))%I
                | None => ((⌜argh = Any.pair false↑ argl /\ o = ord_top⌝): iProp)%I
                end)
             (fun mn ox reth retl =>
                map_or_else ox (fun x => (fs.(postcond) mn x reth retl)) (⌜reth = retl⌝: iProp)%I)
  .

  Definition disclose_ksb_tgt (ksb: kspecbody): fspecbody :=
    mk_specbody (disclose_tgt ksb)
                (fun '(mn, argh) =>
                   '(kf, argh) <- (Any.split argh)ǃ;; kf <- kf↓ǃ;;
                   my_if kf
                         (transl_fun_tgt ksb.(ksb_kbody) (mn, argh))
                         (transl_fun_tgt ksb.(ksb_ubody) (mn, argh)))
  .

  Definition transl_tgt (ms: t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd disclose_ksb_tgt) ms.(fnsems);
    SModSem.mn := ms.(mn);
    SModSem.initial_mr := ms.(initial_mr);
    SModSem.initial_st := ms.(initial_st);
  |}
  .



  Variable (_frds: list mname).
  Let frds: list (option mname) := None :: (List.map Some _frds).

  Definition handle_kCallE_src: kCallE ~> itree Es :=
    fun _ '(kCall kf fn args) =>
      match kf with
      | pure => tau;; trigger (Choose _)
      | impure => trigger (Call fn args)
      end
  .

  Definition interp_kCallE_src: itree (kCallE +' pE +' eventE) ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_kCallE_src)
                  ((fun T X => trigger X): _ ~> itree Es))
  .

  Definition body_to_src {X} (body: X -> itree (kCallE +' pE +' eventE) Any.t): X -> itree Es Any.t :=
    (@interp_kCallE_src _) ∘ body
  .

  Definition disclose_ksb_src (ksb: kspecbody): option string * Any.t -> itree Es Any.t :=
    fun '(mn, argh) =>
      my_if (@in_dec _ (@option_Dec _ _) mn frds) (* why typeclass search fail... *)
            (body_to_src ksb.(ksb_kbody) (mn, argh))
            (body_to_src ksb.(ksb_ubody) (mn, argh))
  .

  Definition transl_src (ms: t): ModSem.t := {|
    ModSem.fnsems := List.map (map_snd disclose_ksb_src) ms.(fnsems);
    ModSem.mn := ms.(mn);
    ModSem.initial_st := ms.(initial_st);
  |}
  .

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma transl_itr_tgt_bind
        (R S: Type)
        (s: itree _ R) (k : R -> itree _ S)
    :
      (transl_itr_tgt (s >>= k))
      =
      ((transl_itr_tgt s) >>= (fun r => transl_itr_tgt (k r))).
  Proof.
    unfold transl_itr_tgt in *. grind.
  Qed.

  Lemma transl_itr_tgt_tau
        (U: Type)
        (t : itree _ U)
    :
      (transl_itr_tgt (Tau t))
      =
      (Tau (transl_itr_tgt t)).
  Proof.
    unfold transl_itr_tgt in *. grind.
  Qed.

  Lemma transl_itr_tgt_ret
        (U: Type)
        (t: U)
    :
      ((transl_itr_tgt (Ret t)))
      =
      Ret t.
  Proof.
    unfold transl_itr_tgt in *. grind.
  Qed.

  Lemma transl_itr_tgt_triggerp
        (R: Type)
        (i: pE R)
    :
      (transl_itr_tgt (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_tgt in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_tgt_triggere
        (R: Type)
        (i: eventE R)
    :
      (transl_itr_tgt (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_tgt in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_tgt_kcall
        (R: Type)
        (i: kCallE R)
    :
      (transl_itr_tgt (trigger i))
      =
      (trigger (transl_kCallE_tgt i) >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_tgt in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_tgt_triggerUB
        (R: Type)
    :
      (transl_itr_tgt (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold transl_itr_tgt, triggerUB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma transl_itr_tgt_triggerNB
        (R: Type)
    :
      (transl_itr_tgt (triggerNB))
      =
      triggerNB (A:=R).
  Proof.
    unfold transl_itr_tgt, triggerNB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma transl_itr_tgt_unwrapU
        (R: Type)
        (i: option R)
    :
      (transl_itr_tgt (unwrapU i))
      =
      (unwrapU i).
  Proof.
    unfold transl_itr_tgt, unwrapU in *. des_ifs.
    { etrans.
      { eapply transl_itr_tgt_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_tgt_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma transl_itr_tgt_unwrapN
        (R: Type)
        (i: option R)
    :
      (transl_itr_tgt (unwrapN i))
      =
      (unwrapN i).
  Proof.
    unfold transl_itr_tgt, unwrapN in *. des_ifs.
    { etrans.
      { eapply transl_itr_tgt_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_tgt_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma transl_itr_tgt_assume
        P
    :
      (transl_itr_tgt (assume P))
      =
      (assume P;;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite transl_itr_tgt_bind. rewrite transl_itr_tgt_triggere. grind. eapply transl_itr_tgt_ret.
  Qed.

  Lemma transl_itr_tgt_guarantee
        P
    :
      (transl_itr_tgt (guarantee P))
      =
      (guarantee P;;; tau;; Ret tt).
  Proof.
    unfold guarantee. rewrite transl_itr_tgt_bind. rewrite transl_itr_tgt_triggere. grind. eapply transl_itr_tgt_ret.
  Qed.

  Lemma transl_itr_tgt_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (transl_itr_tgt itr0)
      =
      (transl_itr_tgt itr1)
  .
  Proof. subst; et. Qed.

  Global Opaque transl_itr_tgt.

  Lemma interp_kCallE_src_bind
        (R S: Type)
        (s: itree _ R) (k : R -> itree _ S)
    :
      (interp_kCallE_src (s >>= k))
      =
      ((interp_kCallE_src s) >>= (fun r => interp_kCallE_src (k r))).
  Proof.
    unfold interp_kCallE_src in *. grind.
  Qed.

  Lemma interp_kCallE_src_tau
        (U: Type)
        (t : itree _ U)
    :
      (interp_kCallE_src (Tau t))
      =
      (Tau (interp_kCallE_src t)).
  Proof.
    unfold interp_kCallE_src in *. grind.
  Qed.

  Lemma interp_kCallE_src_ret
        (U: Type)
        (t: U)
    :
      ((interp_kCallE_src (Ret t)))
      =
      Ret t.
  Proof.
    unfold interp_kCallE_src in *. grind.
  Qed.

  Lemma interp_kCallE_src_triggerp
        (R: Type)
        (i: pE R)
    :
      (interp_kCallE_src (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold interp_kCallE_src in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma interp_kCallE_src_triggere
        (R: Type)
        (i: eventE R)
    :
      (interp_kCallE_src (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold interp_kCallE_src in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma interp_kCallE_src_kcall
        (R: Type)
        (i: kCallE R)
    :
      (interp_kCallE_src (trigger i))
      =
      (handle_kCallE_src i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold interp_kCallE_src in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma interp_kCallE_src_triggerUB
        (R: Type)
    :
      (interp_kCallE_src (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold interp_kCallE_src, triggerUB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma interp_kCallE_src_triggerNB
        (R: Type)
    :
      (interp_kCallE_src (triggerNB))
      =
      triggerNB (A:=R).
  Proof.
    unfold interp_kCallE_src, triggerNB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma interp_kCallE_src_unwrapU
        (R: Type)
        (i: option R)
    :
      (interp_kCallE_src (unwrapU i))
      =
      (unwrapU i).
  Proof.
    unfold interp_kCallE_src, unwrapU in *. des_ifs.
    { etrans.
      { eapply interp_kCallE_src_ret. }
      { grind. }
    }
    { etrans.
      { eapply interp_kCallE_src_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma interp_kCallE_src_unwrapN
        (R: Type)
        (i: option R)
    :
      (interp_kCallE_src (unwrapN i))
      =
      (unwrapN i).
  Proof.
    unfold interp_kCallE_src, unwrapN in *. des_ifs.
    { etrans.
      { eapply interp_kCallE_src_ret. }
      { grind. }
    }
    { etrans.
      { eapply interp_kCallE_src_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma interp_kCallE_src_assume
        P
    :
      (interp_kCallE_src (assume P))
      =
      (assume P;;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite interp_kCallE_src_bind. rewrite interp_kCallE_src_triggere. grind. eapply interp_kCallE_src_ret.
  Qed.

  Lemma interp_kCallE_src_guarantee
        P
    :
      (interp_kCallE_src (guarantee P))
      =
      (guarantee P;;; tau;; Ret tt).
  Proof.
    unfold guarantee. rewrite interp_kCallE_src_bind. rewrite interp_kCallE_src_triggere. grind. eapply interp_kCallE_src_ret.
  Qed.

  Lemma interp_kCallE_src_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (interp_kCallE_src itr0)
      =
      (interp_kCallE_src itr1)
  .
  Proof. subst; et. Qed.

  Global Opaque interp_kCallE_src.

End KMODSEM.
End KModSem.
Coercion KModSem.disclose_ksb_tgt: kspecbody >-> fspecbody.
Coercion KModSem.transl_tgt: KModSem.t >-> SModSem.t.



Section RDB.
  Context `{Σ: GRA.t}.

  Global Program Instance ktransl_itr_tgt_rdb: red_database (mk_box (@KModSem.transl_itr_tgt)) :=
    mk_rdb
      0
      (mk_box KModSem.transl_itr_tgt_bind)
      (mk_box KModSem.transl_itr_tgt_tau)
      (mk_box KModSem.transl_itr_tgt_ret)
      (mk_box KModSem.transl_itr_tgt_kcall)
      (mk_box KModSem.transl_itr_tgt_triggere)
      (mk_box KModSem.transl_itr_tgt_triggerp)
      (mk_box True)
      (mk_box KModSem.transl_itr_tgt_triggerUB)
      (mk_box KModSem.transl_itr_tgt_triggerNB)
      (mk_box KModSem.transl_itr_tgt_unwrapU)
      (mk_box KModSem.transl_itr_tgt_unwrapN)
      (mk_box KModSem.transl_itr_tgt_assume)
      (mk_box KModSem.transl_itr_tgt_guarantee)
      (mk_box KModSem.transl_itr_tgt_ext)
  .

  Global Program Instance ktransl_itr_src_rdb: red_database (mk_box (@KModSem.interp_kCallE_src)) :=
    mk_rdb
      0
      (mk_box KModSem.interp_kCallE_src_bind)
      (mk_box KModSem.interp_kCallE_src_tau)
      (mk_box KModSem.interp_kCallE_src_ret)
      (mk_box KModSem.interp_kCallE_src_kcall)
      (mk_box KModSem.interp_kCallE_src_triggere)
      (mk_box KModSem.interp_kCallE_src_triggerp)
      (mk_box True)
      (mk_box KModSem.interp_kCallE_src_triggerUB)
      (mk_box KModSem.interp_kCallE_src_triggerNB)
      (mk_box KModSem.interp_kCallE_src_unwrapU)
      (mk_box KModSem.interp_kCallE_src_unwrapN)
      (mk_box KModSem.interp_kCallE_src_assume)
      (mk_box KModSem.interp_kCallE_src_guarantee)
      (mk_box KModSem.interp_kCallE_src_ext)
  .

End RDB.

Require Import SimModSem HTactics.
Section KTACTICS.

  Context `{Σ: GRA.t}.

  Lemma APCK_start_clo
        (at_most: Ord.t) (n1: Ord.t)
        (o: ord)
        world w r rg (n0: Ord.t) mp_src0
        mn k_src
        (wf: world -> Any.t * Any.t -> Prop)
        (le: world -> world -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx

        (ATMOST: (at_most < kappa)%ord)
        (FUEL: (n1 + 5 < n0)%ord)

        (POST: gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) rg rg _ _ eqr n1 w
                      (mp_src0,
                       (interp_hCallE_tgt stb mn o (KModSem.transl_itr_tgt (_APCK at_most)) ctx) >>= k_src)
                      (itr_tgt))
    :
      gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) r rg _ _ eqr n0 w
             (mp_src0,
              (interp_hCallE_tgt stb mn o (KModSem.transl_itr_tgt APCK) ctx) >>= k_src)
             (itr_tgt).
  Proof.
    unfold APCK. destruct ctx. destruct itr_tgt.
    steps. force_l.
    exists at_most. ired_l.  _step; [by eauto with ord_step|]. steps; [by eauto with ord_step|].
    unfold guarantee. ired_both. force_l. esplits; et.
    ired_both. _step; [by eauto with ord_step|]. steps; [by eauto with ord_step|]. ss.
    guclo lordC_spec. econs; et. rewrite OrdArith.add_O_r. refl.
  Qed.

  Lemma APCK_step_clo
        (fn: gname) (args: Any.t) (next: Ord.t) (n1: Ord.t)

        (o: ord)
        world w r rg (n0: Ord.t) mp_src0
        mn k_src
        (at_most: Ord.t)
        (wf: world -> Any.t * Any.t -> Prop)
        (le: world -> world -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx0

        (FUEL: (n1 + 11 < n0)%ord)
        (ftsp: fspec)
        (FIND: stb fn = Some (KModSem.disclose_tgt ftsp))
        (NEXT: (next < at_most)%ord)

        (POST: gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) rg rg _ _ eqr n1 w
                      (mp_src0,
                       '(ctx1, _) <- (HoareCall mn true o (KModSem.disclose_tgt ftsp) fn (Any.pair true↑ args) ctx0);;
                       tau;; tau;; (interp_hCallE_tgt mn stb o (KModSem.transl_itr_tgt (_APCK next)) ctx1)
                                     >>= k_src)
                      (itr_tgt))
    :
      gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) r rg _ _ eqr n0 w
             (mp_src0,
              (interp_hCallE_tgt mn stb o (KModSem.transl_itr_tgt (_APCK at_most)) ctx0) >>= k_src)
             (itr_tgt).
  Proof.
    destruct ctx0. destruct itr_tgt.
    rewrite unfold_APCK. steps. force_l. exists false. ired_both.
    _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l. esplits; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l. exists (fn, args). esplits; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    rewrite FIND. ired_both.
    guclo lordC_spec. econs; et. { rewrite OrdArith.add_O_r. refl. }
                                 match goal with
                                 | [SIM: gpaco7 _ _ _ _ _ _ _ _ _ ?i0 _ |- gpaco7 _ _ _ _ _ _ _ _ _ ?i1 _] =>
                                   replace i1 with i0; auto
                                 end.
    f_equal. grind. ired_both. grind. ired_both. grind.
  Qed.

  Lemma APCK_stop_clo
        (n1: Ord.t)

        (o: ord)
        world w r rg (n0: Ord.t) mp_src0
        mn k_src
        (at_most: Ord.t)
        (wf: world -> Any.t * Any.t -> Prop)
        (le: world -> world -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx

        (FUEL: (n1 + 2 < n0)%ord)

        (POST: gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) rg rg _ _ eqr n1 w
                      (mp_src0, k_src (ctx, ()))
                      (itr_tgt))
    :
      gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) r rg _ _ eqr n0 w
             (mp_src0,
              (interp_hCallE_tgt stb mn o (KModSem.transl_itr_tgt (_APCK at_most)) ctx) >>= k_src)
             (itr_tgt).
  Proof.
    destruct ctx. destruct itr_tgt.
    rewrite unfold_APCK. steps. force_l. exists true.
    ired_both; _step; [by eauto with ord_step|].
    ired_both; _step; [by eauto with ord_step|].
    steps.
    guclo lordC_spec. econs; et. { rewrite OrdArith.add_O_r. refl. }
  Qed.

  Lemma trivial_init_clo
        A
        (R_src: A -> Any.t -> Any.t -> iProp) (le: A -> A -> Prop)
        (mn: string) fn f_tgt gstb body
        (POST: forall a mp_src mp_tgt (mr_src: Σ) fr_src ctx varg
                      (ACC: current_iPropL ctx [("INV", R_src a mp_src mp_tgt)])
          ,
            gpaco7 (_sim_itree (mk_wf R_src) le) (cpn7 (_sim_itree (mk_wf R_src) le)) bot7 bot7
                   _ _
                   (lift_rel (mk_wf R_src) le a (@eq Any.t))
                   93 a
                   (Any.pair mp_src mr_src↑,
                    ((interp_hCallE_tgt mn gstb ord_top (KModSem.transl_fun_tgt body varg) (ctx, fr_src))
                       >>= (HoareFunRet (fun (_: option string) (_: unit) (reth retl: Any.t) =>
                                           (⌜reth = retl⌝%I): iProp) (Some mn) tt))
                   )
                   (mp_tgt, (f_tgt varg))
        )
    :
      sim_fnsem (mk_wf R_src) le
                (fn, fun_to_tgt mn gstb (KModSem.disclose_ksb_tgt (mk_kspecbody fspec_trivial body body)))
                (fn, f_tgt)
  .
  Proof.
    init. harg. rename w into aa.
    assert(ord_cur = ord_top).
    { on_current ltac:(fun ACC => clear - ACC); mClear "INV"; des_ifs; mDesAll; des; ss. }
    subst. des_ifs; mDesAll; des; subst.
    - steps. exploit POST; et.
    - steps. exploit POST; et.
  Qed.

End KTACTICS.

Ltac kstart _at_most :=
  eapply (APCK_start_clo) with (at_most := _at_most);
  [eauto with ord_kappa|
   (try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
  ]
.

Ltac kstep _fn _args :=
  eapply (@APCK_step_clo _ _fn _args);
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
   (try by (stb_tac; refl))|
   (eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r)|
  ].

Ltac kcatch :=
  match goal with
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn ?args) >>= _)) ] =>
    kstep fn args
  end.

Ltac kstop :=
  eapply APCK_stop_clo;
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|].

Ltac trivial_init := eapply trivial_init_clo; i; des_u.



Module KMod.
Section KMOD.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: Sk.t -> KModSem.t;
    sk: Sk.t;
  }
  .

  Definition transl_tgt (md: t): SMod.t := {|
    SMod.get_modsem := fun sk => KModSem.transl_tgt (md.(get_modsem) sk);
    SMod.sk := md.(sk);
  |}
  .

  Lemma transl_tgt_comm: forall md sk, KModSem.transl_tgt (md.(get_modsem) sk) =
                                       (transl_tgt md).(SMod.get_modsem) sk.
  Proof. i. refl. Qed.

  Definition transl_src (frds: Sk.t -> list mname) (md: t): Mod.t := {|
    Mod.get_modsem := fun sk => KModSem.transl_src (frds sk) (md.(get_modsem) sk);
    Mod.sk := md.(sk);
  |}
  .

  Lemma transl_src_comm: forall md frds sk, KModSem.transl_src (frds sk) (md.(get_modsem) sk) =
                                            (transl_src frds md).(Mod.get_modsem) sk.
  Proof. i. refl. Qed.

End KMOD.
End KMod.

Coercion KMod.transl_tgt: KMod.t >-> SMod.t.
