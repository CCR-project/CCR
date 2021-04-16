Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Export HoareDef.
Require Import Hoareproof0 Hoareproof1.
Require Import SimModSem.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section AUX________REMOVEME_____REDUNDANT.

  Context `{Σ: GRA.t}.

  Definition refines_closed (md_tgt md_src: ModL.t): Prop :=
    Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_src)
  .

  Global Program Instance refines_closed_PreOrder: PreOrder refines_closed.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. r in H. r in H0. eauto. Qed.

  Lemma refines_close: SimModSem.refines <2= refines_closed.
  Proof. ii. specialize (PR nil). ss. unfold Mod.add_list in *. ss. rewrite ! ModL.add_empty_l in PR. eauto. Qed.

End AUX________REMOVEME_____REDUNDANT.




Section CANCEL.

  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := fold_right Sk.add Sk.unit (List.map SMod.sk mds).
  Let skenv: SkEnv.t := Sk.load_skenv sk.
  Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) skenv) mds).
  Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss).
  Let stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb.

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_tgt: list Mod.t := List.map (SMod.to_tgt stb) mds.



  Let W: Type := (r_state * p_state).
  (* Let wf: Ord.t -> W -> W -> Prop := top3. *)

  Opaque EventsL.interp_Es.

  Let ms_src: ModSemL.t := ModL.enclose (Mod.add_list mds_src).
  Let ms_tgt: ModSemL.t := ModL.enclose (Mod.add_list mds_tgt).

  (* Let rsum: r_state -> Σ := *)
  (*   fun '(mrs_tgt, frs_tgt) => (URA.add (fold_left URA.add (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) *)
  (*                                       (fold_left URA.add frs_tgt ε)). *)
  Let rsum: r_state -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (fold_left (⋅) (List.map (mrs_tgt <*> fst) sbtb) ε) ⋅ (fold_left (⋅) frs_tgt ε).

  Variable entry_r: Σ.
  Variable main_pre: Any.t -> ord -> Σ -> Prop.
  Variable (mainbody: list val -> itree (hCallE +' pE +' eventE) val).
  Hypothesis MAINPRE: main_pre ([]: list val)↑ ord_top entry_r.

  Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)).

  Hypothesis MAINM: In (main_mod main_pre mainbody) mds.

  Theorem adequacy_type: refines_closed (Mod.add_list mds_tgt) (Mod.add_list mds_src).
  Proof. ii. eapply adequacy_type_m2s. eapply adequacy_type_t2m; et. Qed.

End CANCEL.




Require Import Weakening.

Section AUX.

  Context `{Σ: GRA.t}.

  Definition stb_weaker (stb0 stb1: list (gname * fspec)): Prop :=
    forall fn fn0 fsp0 (FINDTGT: List.find (fun '(_fn, _) => dec fn _fn) stb0 = Some (fn0, fsp0)),
    exists fn1 fsp1,
      (<<FINDSRC: List.find (fun '(_fn, _) => dec fn _fn) stb1 = Some (fn1, fsp1)>>) /\
      (<<WEAKER: fspec_weaker fsp0 fsp1>>)
  .

End AUX.




Section CANCEL.

  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := fold_right Sk.add Sk.unit (List.map SMod.sk mds).
  Let skenv: SkEnv.t := Sk.load_skenv sk.
  Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) skenv) mds).
  Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss).
  Let stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb.

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Variable mds_tgt: list Mod.t.
  Hypothesis WEAKEN: Forall2 (fun md md_tgt => exists stb0, (<<WEAK: stb_weaker stb0 stb>>)
                                                            /\ (<<MD: md_tgt = SMod.to_tgt stb0 md>>)) mds mds_tgt.



  Let W: Type := (r_state * p_state).
  (* Let wf: Ord.t -> W -> W -> Prop := top3. *)

  Opaque EventsL.interp_Es.

  Let ms_src: ModSemL.t := ModL.enclose (Mod.add_list mds_src).
  Let ms_tgt: ModSemL.t := ModL.enclose (Mod.add_list mds_tgt).

  (* Let rsum: r_state -> Σ := *)
  (*   fun '(mrs_tgt, frs_tgt) => (URA.add (fold_left URA.add (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) *)
  (*                                       (fold_left URA.add frs_tgt ε)). *)
  Let rsum: r_state -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (fold_left (⋅) (List.map (mrs_tgt <*> fst) sbtb) ε) ⋅ (fold_left (⋅) frs_tgt ε).

  Variable entry_r: Σ.
  Variable main_pre: Any.t -> ord -> Σ -> Prop.
  Variable (mainbody: list val -> itree (hCallE +' pE +' eventE) val).
  Hypothesis MAINPRE: main_pre ([]: list val)↑ ord_top entry_r.

  Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)).

  Hypothesis MAINM: In (main_mod main_pre mainbody) mds.

  Let initial_mrs_eq_aux
      skenv0
    :
      List.map
        (fun x =>
           (SModSem.mn (SMod.get_modsem x skenv0),
            (SModSem.initial_mr (SMod.get_modsem x skenv0), SModSem.initial_st (SMod.get_modsem x skenv0)))) mds =
      ModSemL.initial_mrs (ModL.get_modsem (Mod.add_list mds_tgt) skenv0)
  .
  Proof.
    clear - WEAKEN.
    eapply Forall2_impl in WEAKEN; cycle 1.
    { instantiate (1:=(fun md md_tgt => exists stb0, (<<MD: md_tgt = SMod.to_tgt stb0 md>>))).
      ii. ss. des. subst. eauto. }
    induction WEAKEN; ss.
    des; subst. ss.
    f_equal; ss.
    eapply IHn.
    inv WEAKEN; ss.
  Qed.

  Lemma sk_eq: fold_right Sk.add Sk.unit (List.map SMod.sk mds) = ModL.sk (Mod.add_list mds_tgt).
  Proof.
    clear - WEAKEN.
    eapply Forall2_impl in WEAKEN; cycle 1.
    { instantiate (1:=(fun md md_tgt => exists stb0, (<<MD: md_tgt = SMod.to_tgt stb0 md>>))).
      ii. ss. des. subst. eauto. }
    induction WEAKEN; ss. des; subst. ss.
    f_equal. erewrite IHn; ss.
  Qed.

  Lemma initial_mrs_eq
    :
      List.map
        (fun x =>
           (SModSem.mn (SMod.get_modsem x skenv),
            (SModSem.initial_mr (SMod.get_modsem x skenv), SModSem.initial_st (SMod.get_modsem x skenv)))) mds =
      ModSemL.initial_mrs (ModL.enclose (Mod.add_list mds_tgt))
  .
  Proof.
    unfold ModL.enclose.
    erewrite initial_mrs_eq_aux. repeat f_equal. unfold skenv, sk. ss.
    f_equal. rewrite sk_eq. ss.
  Qed.

  (* Definition load_fnsems (skenv: SkEnv.t) (md: SMod.t) (tr0: fspecbody -> Any.t -> itree Es Any.t): *)
  (*   list (string * (Any.t -> itree Es Any.t)) := *)
  (*   let ms := (SMod.get_modsem md skenv) in *)
  (*   List.map (ModSem.map_snd tr0) ms.(SModSem.fnsems) *)
  (* . *)

  (* Lemma transl_fnsems_aux *)
  (*       tr0 mr0 md *)
  (*       (skenv0: SkEnv.t) *)
  (*   : *)
  (*     (ModSem.fnsems (Mod.get_modsem (SMod.transl tr0 mr0 md) skenv0)) = *)
  (*     (load_fnsems skenv0 md tr0) *)
  (* . *)
  (* Proof. refl. Qed. *)

  (* Lemma transl_fnsems *)
  (*       tr0 mr0 mds *)
  (*   : *)
  (*     (ModSem.fnsems (Mod.get_modsem (SMod.transl tr0 mr0 md) skenv0)) = *)
  (*     (load_fnsems skenv0 md tr0) *)
  (*     (ModSemL.fnsems (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds)))) = *)
  (*     (load_fnsems (Sk.load_skenv (List.fold_right Sk.add Sk.unit (List.map sk mds))) mds tr0) *)
  (* . *)
  (* Proof. *)
  (*   unfold ModL.enclose. *)
  (*   rewrite transl_fnsems_aux. do 2 f_equal. rewrite transl_sk. ss. *)
  (* Qed. *)

  Theorem adequacy_type2: refines_closed (Mod.add_list mds_tgt) (Mod.add_list mds_src).
  Proof.
    etrans; cycle 1.
    { eapply adequacy_type; et. des_ifs. ss.
      folder.
      unfold ModSemL.initial_r_state in Heq. unfold SMod.to_tgt in Heq. clarify.
      rewrite SMod.transl_initial_mrs. ss. folder.
      rp; et. repeat f_equal. apply func_ext. intro mn.
      assert(T: (SMod.load_initial_mrs skenv mds SModSem.initial_mr) = (ModSemL.initial_mrs ms_tgt)).
      { unfold SMod.load_initial_mrs. unfold ms_tgt.
        rewrite SMod.red_do_ret. rewrite initial_mrs_eq. ss.
      }
      rewrite T; ss.
    }
    folder.
    eapply refines_close.
    eapply adequacy_local_list.
    (* clear initial_mrs_eq_aux WFR MAINM MAINPRE. clear_tac. *)
    clear - WEAKEN.
    clearbody stb.
    clear sk skenv mss sbtb.
    induction WEAKEN; ss.
    des; subst. rename l into ll. econs; cycle 1.
    { eapply IHf. ss. }

    clear - WEAK.
    econs; cycle 1.
    { unfold SMod.to_tgt. cbn. eauto. }
    { i. admit "ez - wf". }
    i. r. eapply adequacy_lift. econs.
    { instantiate (1:=fun '(x, y) => x = y).
      unfold SMod.to_tgt.
      unfold SMod.transl. ss.
      rename x into md.
      abstr (SModSem.fnsems (SMod.get_modsem md skenv)) fnsems.
      induction fnsems; ss.
      econs; et. destruct a. cbn. split; cbn.
      { rr. cbn. ss. }
      r. cbn.
      destruct f.
      replace (fun '(x, y) => x = y) with
          (fun '(mrps_src0, mrps_tgt0) => exists (mr: Σ) (mp: Any.t), (<<SRC: mrps_src0 = (mr, mp)>>)
                                                                      /\ <<TGT: mrps_tgt0 = (mr, mp)>>); cycle 1.
      { apply func_ext. i. des_ifs. apply prop_ext. split; i; des; subst; et. destruct p0. esplits; et. }
      eapply weakening_fn; ss.
      refl.
    }
    { ss. }
    { ss. }
  Qed.

End CANCEL.
