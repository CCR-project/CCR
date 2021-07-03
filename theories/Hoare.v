Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Export HoareDef STB.
Require Import Hoareproof0 Hoareproof1 Hoareproof2.
Require Import SimModSem Logic.

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

Lemma Forall2_eq
      A
      (xs0 xs1: list A)
      (EQ: Forall2 eq xs0 xs1)
  :
    <<EQ: xs0 = xs1>>
.
Proof. induction EQ; ss. des; subst. refl. Qed.

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











Section CANCEL.

  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := Sk.sort (fold_right Sk.add Sk.unit (List.map SMod.sk mds)).
  (* Let skenv: SkEnv.t := Sk.load_skenv sk. *)

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
      (<<NONE: stb sk fn = None>>) \/ (exists fsp, <<FIND: stb sk fn = Some fsp>> /\ <<TRIVIAL: forall mn x arg_src arg_tgt o r (PRE: fsp.(precond) mn x arg_src arg_tgt o r), o = ord_top>>).

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

  Theorem adequacy_type_arg
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb sk "main" = Some main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) None x (@initial_arg CONFS) (@initial_arg CONFT) ord_top entry_r>>) /\
               (<<WFR: URA.wf (entry_r ⋅ fold_left (⋅) (List.map SModSem.initial_mr mss) ε)>>) /\
               (<<RET: forall ret_src ret_tgt r
                              (POST: main_fsp.(postcond) None x ret_src ret_tgt r),
                   ret_src = ret_tgt>>))
    :
      Beh.of_program (@ModL.compile CONFT (Mod.add_list mds_tgt)) <1=
      Beh.of_program (@ModL.compile CONFS (Mod.add_list mds_src)).
  Proof.
    ii. eapply adequacy_type_m2s.
    eapply adequacy_type_m2m; et.
    eapply adequacy_type_t2m; et.
    Unshelve.
    all:ss.
  Qed.
  End STRONGER.


  Context {CONF: EMSConfig}.
  Variable entry_r: Σ.
  Variable mainpre: Any.t -> ord -> Σ -> Prop.
  Hypothesis MAINPRE: mainpre initial_arg ord_top entry_r.

  Hypothesis WFR: URA.wf (entry_r ⋅ fold_left (⋅) (List.map SModSem.initial_mr mss) ε).

  Hypothesis MAINM: stb sk "main" = Some (mk_simple (fun _ : () => (mainpre, fun _ => (⌜True⌝: iProp)%I))).

  Theorem adequacy_type: refines_closed (Mod.add_list mds_tgt) (Mod.add_list mds_src).
  Proof.
    ii. eapply adequacy_type_arg; et.
    i. clarify. esplits; et.
    { ss. uipropall. split; auto. red. uipropall. }
    { i. ss. red in POST. uipropall. des. red in POST0. uipropall. }
    Unshelve. ss.
  Qed.

End CANCEL.




Require Import Weakening.
Require Import ClassicalChoice.

Section CANCEL.

  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.


  Let sk: Sk.t := Sk.sort (fold_right Sk.add Sk.unit (List.map SMod.sk mds)).
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
    erewrite initial_mrs_eq_aux. repeat f_equal. unfold sk, sk. ss.
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
  Lemma adequacy_type2
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb "main" = Some main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) None x initial_arg initial_arg ord_top entry_r>>) /\
               (<<WFR: URA.wf (entry_r ⋅ fold_left (⋅) (List.map SModSem.initial_mr mss) ε)>>) /\
               (<<RET: forall ret_src ret_tgt r
                              (POST: main_fsp.(postcond) None x ret_src ret_tgt r),
                   ret_src = ret_tgt>>))
    :
      refines_closed (Mod.add_list mds_tgt) (Mod.add_list mds_src).
  Proof.
    ii. eapply adequacy_type_arg; ss.
    { instantiate (1:=fun _ => stb). unfold stb. i.
      unfold _stb, _sbtb, _mss, sk. rewrite FIND. auto. }
    { i. unfold stb, _stb, _sbtb, _mss, sk. rewrite FIND.
      right. esplits; et. ii. red in PRE. ss. red in PRE. uipropall. des; auto. }
    { i. fold stb. hexploit MAINM; et.  }
    { revert x0 PR.
      eapply refines_close.
      eapply adequacy_local_list.
      rewrite <- map_id. eapply Forall2_apply_Forall2; et.
      i. ss. des. subst. eapply adequacy_weaken; et.
    }
  Qed.

End CANCEL.
