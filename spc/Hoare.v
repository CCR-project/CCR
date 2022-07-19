Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Export HoareDef STB.
Require Import Hoareproof0 Hoareproof1 Hoareproof2.
Require Import SimModSem ProofMode.

Set Implicit Arguments.



Lemma fold_right_map
      XS XI YS YI
      (xs: XS) (xi: list XI)
      (xadd: XI -> XS -> XS)

      (* (ys: YS) (yi: list YI) *)
      (yadd: YI -> YS -> YS)

      (fs: XS -> YS)
      (fi: XI -> YI)
      (HOM: forall xi xs, fs (xadd xi xs) = yadd (fi xi) (fs xs))
  :
    <<EQ: fs (fold_right xadd xs xi) = fold_right yadd (fs xs) (List.map fi xi)>>
.
Proof.
  r. ginduction xi; ii; ss.
  rewrite HOM. f_equal. eapply IHxi; et.
Qed.

(*** TODO: move to Coqlib ***)
Lemma find_app
      X (xs0 xs1: list X) (f: X -> bool) x
      (FIND: find f xs0 = Some x)
  :
    <<FIND: find f (xs0 ++ xs1) = Some x>>
.
Proof.
  revert_until xs0. induction xs0; ii; ss. des_ifs. erewrite IHxs0; et.
Qed.











Section CANCELSTB.

  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := SMod.get_sk mds.

  Let _mss: Sk.t -> list SModSem.t := fun sk => (List.map ((flip SMod.get_modsem) sk) mds).
  Let _sbtb: Sk.t -> list (gname * fspecbody) := fun sk => (List.flat_map (SModSem.fnsems) (_mss sk)).
  Let _stb: Sk.t -> list (gname * fspec) := fun sk => List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) (_sbtb sk).

  Let mss: list SModSem.t := _mss sk.
  Let sbtb: list (gname * fspecbody) := _sbtb sk.

  Variable stb: Sk.t -> gname -> option fspec.
  Hypothesis STBCOMPLETE:
    forall fn fsp (FIND: alist_find fn (_stb sk) = Some fsp), stb sk fn = Some fsp.
  Hypothesis STBSOUND:
    forall fn (FIND: alist_find fn (_stb sk) = None),
      (<<NONE: stb sk fn = None>>) \/ (exists fsp, <<FIND: stb sk fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>).

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_tgt: list Mod.t := List.map (SMod.to_tgt stb) mds.



  Let W: Type := p_state.
  (* Let wf: Ord.t -> W -> W -> Prop := top3. *)

  Opaque EventsL.interp_Es.

  Let ms_src: ModSemL.t := ModL.enclose (Mod.add_list mds_src).
  Let ms_tgt: ModSemL.t := ModL.enclose (Mod.add_list mds_tgt).

  Section STRONGER.
  Context {CONFS CONFT: EMSConfig}.
  Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

  Theorem adequacy_type_arg_stb
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb sk "main" = Some main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) None x (@initial_arg CONFS) (@initial_arg CONFT) entry_r>>) /\
               (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
               (<<WFR: URA.wf (entry_r ⋅ fold_left (⋅) (List.map SModSem.initial_mr mss) ε)>>) /\
               (<<RET: forall ret_src ret_tgt,
                   ((main_fsp.(postcond) None x ret_src ret_tgt: iProp) -∗ ⌜ret_src = ret_tgt⌝)>>))
    :
      Beh.of_program (@ModL.compile _ CONFT (Mod.add_list mds_tgt)) <1=
      Beh.of_program (@ModL.compile _ CONFS (Mod.add_list mds_src)).
  Proof.
    ii. eapply adequacy_type_m2s; et.
    eapply adequacy_type_m2m; et.
    eapply adequacy_type_t2m; et.
    i. exploit MAINM; et. i. des. esplits; et.
    i. specialize (RET ret_src ret_tgt). uipropall.
    hexploit RET; et. i. rr in H. uipropall.
    all:ss.
  Qed.
  End STRONGER.


  Context {CONF: EMSConfig}.
  Variable entry_r: Σ.

  Hypothesis WFR: URA.wf (entry_r ⋅ SMod.get_initial_mrs mds sk).

  Hypothesis MAINM: forall (main_fsp: fspec) (MAIN: stb sk "main" = Some main_fsp),
      exists (x: main_fsp.(meta)),
        (<<PRE: Own (entry_r) -∗ main_fsp.(precond) None x initial_arg initial_arg>>) /\
        (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
        (<<RET: forall ret_src ret_tgt,
            (main_fsp.(postcond) None x ret_src ret_tgt: iProp) -∗ (⌜ret_src = ret_tgt⌝)>>).

  Theorem adequacy_type_stb: refines_closed (Mod.add_list mds_tgt) (Mod.add_list mds_src).
  Proof.
    ii. eapply adequacy_type_arg_stb; et.
    i. hexploit MAINM; et. i. des. esplits; et.
    { eapply to_semantic.
      { eapply PRE.  }
      { eapply URA.wf_mon; et. }
    }
    { r_wf WFR. unfold SMod.get_initial_mrs. ss. unfold mss, _mss.
      rewrite List.map_map. ss. }
  Qed.

End CANCELSTB.


Section CANCEL.

  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := SMod.get_sk mds.
  Let stb0: Sk.t -> gname -> option fspec := fun sk => to_stb (SMod.get_stb mds sk).
  Let stb1: Sk.t -> gname -> option fspec := fun sk => to_closed_stb (SMod.get_stb mds sk).

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_tgt0: list Mod.t := List.map (SMod.to_tgt stb0) mds.
  Let mds_tgt1: list Mod.t := List.map (SMod.to_tgt stb1) mds.

  Section STRONGER.
  Context {CONFS CONFT: EMSConfig}.
  Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

  Theorem adequacy_type_arg
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb0 sk "main" = Some main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) None x (@initial_arg CONFS) (@initial_arg CONFT) entry_r>>) /\
               (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
               (<<WFR: URA.wf (entry_r ⋅ SMod.get_initial_mrs mds sk)>>) /\
               (<<RET: forall ret_src ret_tgt,
                   ((main_fsp.(postcond) None x ret_src ret_tgt: iProp) -∗ ⌜ret_src = ret_tgt⌝)>>))
    :
      Beh.of_program (@ModL.compile _ CONFT (Mod.add_list mds_tgt0)) <1=
      Beh.of_program (@ModL.compile _ CONFS (Mod.add_list mds_src)).
  Proof.
    eapply adequacy_type_arg_stb; et.
    { unfold stb0, sk, SMod.get_stb, SMod.get_sk. unfold to_stb.
      rewrite flat_map_map. ss. }
    { i. left. rewrite <- FIND.
      unfold stb0, to_stb, SMod.get_stb.
      rewrite flat_map_map. ss. }
    { i. hexploit MAINM; et. i. des. esplits; et.
      r_wf WFR. rewrite map_map. ss. }
  Qed.

  Theorem adequacy_type_arg_closed
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb1 sk "main" = Some main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) None x (@initial_arg CONFS) (@initial_arg CONFT) entry_r>>) /\
               (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
               (<<WFR: URA.wf (entry_r ⋅ SMod.get_initial_mrs mds sk)>>) /\
               (<<RET: forall ret_src ret_tgt,
                   ((main_fsp.(postcond) None x ret_src ret_tgt: iProp) -∗ ⌜ret_src = ret_tgt⌝)>>))
    :
      Beh.of_program (@ModL.compile _ CONFT (Mod.add_list mds_tgt1)) <1=
      Beh.of_program (@ModL.compile _ CONFS (Mod.add_list mds_src)).
  Proof.
    eapply adequacy_type_arg_stb; et.
    { unfold stb1, sk, SMod.get_stb, SMod.get_sk. unfold to_closed_stb.
      rewrite flat_map_map. i. ss. unfold map_snd. rewrite FIND. auto. }
    { unfold stb1, sk, SMod.get_stb, SMod.get_sk. unfold to_closed_stb.
      rewrite flat_map_map. ss. i. right. unfold map_snd.
      rewrite FIND. esplits; et. }
    { i. exploit MAINM; et. i. des. esplits; et.
      r_wf WFR. rewrite map_map. ss. }
  Qed.
  End STRONGER.

  Context {CONF: EMSConfig}.
  Variable entry_r: Σ.

  Hypothesis WFR: URA.wf (entry_r ⋅ SMod.get_initial_mrs mds sk).

  Section TYPE0.
  Hypothesis MAINM: forall (main_fsp: fspec) (MAIN: stb0 sk "main" = Some main_fsp),
      exists (x: main_fsp.(meta)),
        (<<PRE: Own (entry_r) -∗ main_fsp.(precond) None x initial_arg initial_arg>>) /\
        (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
        (<<RET: forall ret_src ret_tgt,
            (main_fsp.(postcond) None x ret_src ret_tgt: iProp) -∗ (⌜ret_src = ret_tgt⌝)>>).

  Theorem adequacy_type: refines_closed (Mod.add_list mds_tgt0) (Mod.add_list mds_src).
  Proof.
    ii. eapply adequacy_type_arg; et.
    i. hexploit MAINM; et. i. des. esplits; et.
    { eapply to_semantic.
      { uipropall. }
      { eapply URA.wf_mon; et. }
    }
  Qed.
  End TYPE0.


  Section TYPE1.
  Hypothesis MAINM: forall (main_fsp: fspec) (MAIN: stb1 sk "main" = Some main_fsp),
      exists (x: main_fsp.(meta)),
        (<<PRE: Own (entry_r) -∗ main_fsp.(precond) None x initial_arg initial_arg>>) /\
        (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
        (<<RET: forall ret_src ret_tgt,
            (main_fsp.(postcond) None x ret_src ret_tgt: iProp) -∗ (⌜ret_src = ret_tgt⌝)>>).

  Theorem adequacy_type_closed: refines_closed (Mod.add_list mds_tgt1) (Mod.add_list mds_src).
  Proof.
    ii. eapply adequacy_type_arg_closed; et.
    i. hexploit MAINM; et. i. des. esplits; et.
    { eapply to_semantic.
      { uipropall. }
      { eapply URA.wf_mon; et. }
    }
  Qed.
  End TYPE1.

End CANCEL.




Require Import Weakening.
Require Import ClassicalChoice.

Section CANCEL.

  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.


  Let sk: Sk.t := SMod.get_sk mds.
  (* Let sk: Sk.t := Sk.sort (fold_right Sk.add Sk.unit (List.map SMod.sk mds)). *)
  (* Let skenv: SkEnv.t := Sk.load_skenv sk. *)

  Let _mss: Sk.t -> list SModSem.t := fun sk => (List.map ((flip SMod.get_modsem) sk) mds).
  Let _sbtb: Sk.t -> list (gname * fspecbody) := fun sk => (List.flat_map (SModSem.fnsems) (_mss sk)).
  Let _stb: Sk.t -> list (gname * fspec) := fun sk => List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) (_sbtb sk).

  Let mss: list SModSem.t := _mss sk.
  Let sbtb: list (gname * fspecbody) := _sbtb sk.

  Let stb: gname -> option fspec :=
    fun fn => match alist_find fn (_stb sk) with
              | Some fsp => Some fsp
              | None => Some fspec_trivial
              end.

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Variable mds_tgt: list Mod.t.


  Hypothesis WEAKEN: Forall2 (fun md md_tgt => exists stb0, (<<WEAK: forall sk, stb_weaker (stb0 sk) stb>>)
                                                            /\ (<<MD: md_tgt = SMod.to_tgt stb0 md>>)) mds mds_tgt.

  Opaque EventsL.interp_Es.

  Let ms_src: ModSemL.t := ModL.enclose (Mod.add_list mds_src).
  Let ms_tgt: ModSemL.t := ModL.enclose (Mod.add_list mds_tgt).

  Let initial_mrs_eq_aux
      sk0
    :
      List.map
        (fun x =>
           (SModSem.mn (SMod.get_modsem x sk0),
            (Any.pair (SModSem.initial_st (SMod.get_modsem x sk0)) (SModSem.initial_mr (SMod.get_modsem x sk0))↑))) mds =
      ModSemL.initial_mrs (ModL.get_modsem (Mod.add_list mds_tgt) sk0)
  .
  Proof.
    clear - WEAKEN.
    eapply Forall2_impl in WEAKEN; cycle 1.
    { instantiate (1:=(fun md md_tgt => exists stb0, (<<MD: md_tgt = SMod.to_tgt stb0 md>>))).
      ii. ss. des. subst. eauto. }
    induction WEAKEN; ss.
    des; subst. ss.
    f_equal; ss.
    eapply IHf.
    inv WEAKEN; ss.
  Qed.

  Lemma sk_eq: fold_right Sk.add Sk.unit (List.map SMod.sk mds) = ModL.sk (Mod.add_list mds_tgt).
  Proof.
    clear - WEAKEN.
    eapply Forall2_impl in WEAKEN; cycle 1.
    { instantiate (1:=(fun md md_tgt => exists stb0, (<<MD: md_tgt = SMod.to_tgt stb0 md>>))).
      ii. ss. des. subst. eauto. }
    induction WEAKEN; ss. des; subst. ss.
    f_equal. erewrite IHf; ss.
  Qed.

  Lemma sk_eq2: fold_right Sk.add Sk.unit (List.map SMod.sk mds) = (ModL.sk (Mod.add_list (List.map (SMod.to_tgt (fun _ => stb)) mds))).
  Proof.
    rewrite sk_eq. clear - WEAKEN.
    eapply Forall2_impl in WEAKEN; cycle 1.
    { instantiate (1:=(fun md md_tgt => exists stb0, (<<MD: md_tgt = SMod.to_tgt stb0 md>>))).
      ii. ss. des. subst. eauto. } des.
    unfold Mod.add_list.
    erewrite fold_right_map with (fi:=ModL.sk) (fs:=ModL.sk) (yadd:=Sk.add); try refl; cycle 1.
    erewrite fold_right_map with (fi:=ModL.sk) (fs:=ModL.sk) (yadd:=Sk.add); try refl; cycle 1.
    f_equal.
    rewrite ! List.map_map.
    eapply Forall2_apply_Forall2 with (Q:=eq) (f:=ModL.sk ∘ (SMod.to_tgt (fun _ => stb))) (g:=(ModL.sk ∘ Mod.lift)) in WEAKEN.
    { eapply Forall2_eq in WEAKEN. des; ss. }
    ii. des. subst. ss.
  Qed.

  Lemma initial_mrs_eq
    :
      List.map
        (fun x =>
           (SModSem.mn (SMod.get_modsem x sk),
            (Any.pair (SModSem.initial_st (SMod.get_modsem x sk))) (SModSem.initial_mr (SMod.get_modsem x sk))↑)) mds =
      ModSemL.initial_mrs (ModL.enclose (Mod.add_list mds_tgt))
  .
  Proof.
    unfold ModL.enclose.
    erewrite initial_mrs_eq_aux. repeat f_equal. unfold sk, SMod.get_sk.
    f_equal. rewrite sk_eq. ss.
  Qed.

  Lemma initial_mrs_eq2
    :
      List.map fst (ModSemL.initial_mrs ms_tgt) =
      List.map fst (ModSemL.initial_mrs (ModL.enclose (Mod.add_list (List.map (SMod.to_tgt (fun _ => stb)) mds))))
  .
  Proof.
    unfold ms_tgt. rewrite <- initial_mrs_eq.
    unfold ModL.enclose. rewrite <- sk_eq2. folder.
    unfold Mod.add_list.
    match goal with
    | [ |- context[ModL.get_modsem ?x ?sk] ] =>
      replace (ModL.get_modsem x sk) with (((flip ModL.get_modsem) sk) x) by refl
    end.
    erewrite fold_right_map with (yadd:=ModSemL.add) (fi:=(flip ModL.get_modsem) sk); cycle 1.
    { refl. }
    erewrite fold_right_map with (yadd:=@List.app _) (fi:=ModSemL.initial_mrs); cycle 1.
    { refl. }
    rewrite ! List.map_map. cbn.
    clear - mds. clearbody sk.
    induction mds; ii; ss. f_equal; ss.
  Qed.

  Context {CONF: EMSConfig}.
  Lemma adequacy_type2 entry_r
        (WFR: URA.wf (entry_r ⋅ SMod.get_initial_mrs mds sk))
        (MAINM:
           forall (main_fsp: fspec) (MAIN: stb "main" = Some main_fsp),
           exists (x: main_fsp.(meta)),
             (<<PRE: Own entry_r -∗ main_fsp.(precond) None x initial_arg initial_arg>>) /\
             (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
             (<<RET: forall ret_src ret_tgt,
                 (main_fsp.(postcond) None x ret_src ret_tgt: iProp) -∗ (⌜ret_src = ret_tgt⌝)>>))
    :
      refines_closed (Mod.add_list mds_tgt) (Mod.add_list mds_src).
  Proof.
    ii. eapply adequacy_type_arg_stb; ss.
    { instantiate (1:=fun _ => stb). unfold stb. i.
      unfold _stb, _sbtb, _mss, sk. rewrite FIND. auto. }
    { i. unfold stb, _stb, _sbtb, _mss, sk. rewrite FIND.
      right. esplits; et. }
    { i. ss. hexploit MAINM; et. i. des. esplits; et.
      { eapply to_semantic; et.
        eapply URA.wf_mon; et. }
      { r_wf WFR. unfold SMod.get_initial_mrs. rewrite map_map. ss. }
    }
    { revert x0 PR. eapply refines_close. eapply refines2_pairwise.
      rewrite <- (map_id mds_tgt). rewrite <- Forall2_flip.
      eapply Forall2_apply_Forall2; et.
      i. ss. des. subst. eapply adequacy_weaken; et.
    }
  Qed.

End CANCEL.
