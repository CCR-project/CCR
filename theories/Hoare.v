Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Export HoareDef STB.
Require Import Hoareproof0 Hoareproof1.
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
  Let stb: list (gname * fspec) := _stb sk.

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_tgt: list Mod.t := List.map (SMod.to_tgt _stb) mds.



  Let W: Type := (r_state * p_state).
  (* Let wf: Ord.t -> W -> W -> Prop := top3. *)

  Opaque EventsL.interp_Es.

  Let ms_src: ModSemL.t := ModL.enclose (Mod.add_list mds_src).
  Let ms_tgt: ModSemL.t := ModL.enclose (Mod.add_list mds_tgt).

  (* Let rsum: r_state -> Σ := *)
  (*   fun '(mrs_tgt, frs_tgt) => (URA.add (fold_left URA.add (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) *)
  (*                                       (fold_left URA.add frs_tgt ε)). *)
  Let rsum: r_state -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (fold_left (⋅) (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) ⋅ (fold_left (⋅) frs_tgt ε).

  Variable entry_r: Σ.
  Variable mainpre: Any.t -> ord -> Σ -> Prop.
  Variable (mainbody: (option mname * Any.t) -> itree (hCallE +' pE +' eventE) Any.t).
  Hypothesis MAINPRE: mainpre ([]: list val)↑ ord_top entry_r.

  Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)).

  Hypothesis MAINM: alist_find "main" sbtb = Some (mk_specbody (mk_simple (fun _ : () => (mainpre, fun _ => (⌜True⌝: iProp)%I))) mainbody).

  Theorem adequacy_type: refines_closed (Mod.add_list mds_tgt) (Mod.add_list mds_src).
  Proof.
    ii. eapply adequacy_type_m2s; et.
    eapply adequacy_type_t2m; et.
    Unshelve.
    all:ss.
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
  Let stb: list (gname * fspec) := _stb sk.

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Variable mds_tgt: list Mod.t.
  Hypothesis WEAKEN: Forall2 (fun md md_tgt => exists stb0, (<<WEAK: forall sk, stb_weaker (stb0 sk) (_stb sk)>>)
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
    fun '(mrs_tgt, frs_tgt) => (fold_left (⋅) (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) ⋅ (fold_left (⋅) frs_tgt ε).

  Variable entry_r: Σ.
  Variable mainpre: Any.t -> ord -> Σ -> Prop.
  Variable (mainbody: (option mname * Any.t) -> itree (hCallE +' pE +' eventE) Any.t).
  Hypothesis MAINPRE: mainpre ([]: list val)↑ ord_top entry_r.

  Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)).

  Hypothesis MAINM: alist_find "main" sbtb = Some (mk_specbody (mk_simple (fun _ : () => (mainpre, fun _ => (⌜True⌝: iProp)%I))) mainbody).

  Let initial_mrs_eq_aux
      sk0
    :
      List.map
        (fun x =>
           (SModSem.mn (SMod.get_modsem x sk0),
            (SModSem.initial_mr (SMod.get_modsem x sk0), SModSem.initial_st (SMod.get_modsem x sk0)))) mds =
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

  (* Lemma sk_fold_comm *)
  (*       md0 mds0 *)
  (*   : *)
  (*     <<EQ: ModL.sk (fold_right ModL.add md0 mds0) = (fold_right Sk.add (ModL.sk md0) (List.map ModL.sk mds0))>> *)
  (* . *)
  (* Proof. *)
  (* Qed. *)

  Lemma sk_eq2: fold_right Sk.add Sk.unit (List.map SMod.sk mds) = (ModL.sk (Mod.add_list (List.map (SMod.to_tgt _stb) mds))).
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
    eapply Forall2_apply_Forall2 with (Q:=eq) (f:=ModL.sk ∘ (SMod.to_tgt _stb)) (g:=(ModL.sk ∘ Mod.lift)) in WEAKEN.
    { eapply Forall2_eq in WEAKEN. des; ss. }
    ii. des. subst. ss.
  Qed.

  Lemma initial_mrs_eq
    :
      List.map
        (fun x =>
           (SModSem.mn (SMod.get_modsem x sk),
            (SModSem.initial_mr (SMod.get_modsem x sk), SModSem.initial_st (SMod.get_modsem x sk)))) mds =
      ModSemL.initial_mrs (ModL.enclose (Mod.add_list mds_tgt))
  .
  Proof.
    unfold ModL.enclose.
    erewrite initial_mrs_eq_aux. repeat f_equal. unfold sk, sk. ss.
    f_equal. rewrite sk_eq. ss.
  Qed.

  (* Let initial_mrs_eq2_aux sk0 stb0 *)
  (*   : *)
  (*     List.map fst (ModSemL.initial_mrs (ModL.get_modsem (Mod.add_list mds_tgt) sk0)) = *)
  (*     List.map fst (ModSemL.initial_mrs (ModL.get_modsem (Mod.add_list (List.map (SMod.to_tgt stb0) mds)) sk0)) *)
  (* . *)
  (* Proof. *)
  (*   unfold mds_tgt. rewrite <- initial_mrs_eq. *)
  (*   clear. *)
  (*   induction mds; ss. *)
  (* Qed. *)




  (* Declare Scope l_monad_scope. *)
  (* Local Open Scope l_monad_scope. *)
  (* Notation "'do' X <- A ; B" := (List.flat_map (fun X => B) A) : l_monad_scope. *)
  (* Notation "'do' ' X <- A ; B" := (List.flat_map (fun _x => match _x with | X => B end) A) : l_monad_scope. *)
  (* Notation "'ret'" := (fun X => [X]) (at level 60) : l_monad_scope. *)

  Lemma initial_mrs_eq2
    :
      List.map fst (ModSemL.initial_mrs ms_tgt) =
      List.map fst (ModSemL.initial_mrs (ModL.enclose (Mod.add_list (List.map (SMod.to_tgt _stb) mds))))
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

  (* Definition load_fnsems (sk: Sk.t) (md: SMod.t) (tr0: fspecbody -> Any.t -> itree Es Any.t): *)
  (*   list (string * (Any.t -> itree Es Any.t)) := *)
  (*   let ms := (SMod.get_modsem md sk) in *)
  (*   List.map (ModSem.map_snd tr0) ms.(SModSem.fnsems) *)
  (* . *)

  (* Lemma transl_fnsems_aux *)
  (*       tr0 mr0 md *)
  (*       (sk0: Sk.t) *)
  (*   : *)
  (*     (ModSem.fnsems (Mod.get_modsem (SMod.transl tr0 mr0 md) sk0)) = *)
  (*     (load_fnsems sk0 md tr0) *)
  (* . *)
  (* Proof. refl. Qed. *)

  (* Lemma transl_fnsems *)
  (*       tr0 mr0 mds *)
  (*   : *)
  (*     (ModSem.fnsems (Mod.get_modsem (SMod.transl tr0 mr0 md) sk0)) = *)
  (*     (load_fnsems sk0 md tr0) *)
  (*     (ModSemL.fnsems (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds)))) = *)
  (*     (load_fnsems (Sk.load_sk (List.fold_right Sk.add Sk.unit (List.map sk mds))) mds tr0) *)
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
      rp; et.
      (* Check (fun mn : string => *)
      (* match find (fun mnr : string * (Σ * Any.t) => dec mn (fst mnr)) (SMod.load_initial_mrs sk mds SModSem.initial_mr) with *)
      (* | Some r => fst (snd r) *)
      (* | None => ε *)
      (* end). *)
      repeat match goal with
      | |- context[List.map (?gg <*> ?ff) _] => erewrite <- List.map_map with (f:=ff) (g:=gg)
      end.
      erewrite initial_mrs_eq2.
      assert(T: (SMod.load_initial_mrs sk mds SModSem.initial_mr) = (ModSemL.initial_mrs ms_tgt)).
      { unfold SMod.load_initial_mrs. unfold ms_tgt.
        rewrite SMod.red_do_ret. rewrite initial_mrs_eq. ss.
      }
      rewrite T; ss.
    }
    cut (refines_closed (Mod.add_list mds_tgt)
                        (Mod.add_list (List.map (SMod.to_tgt _stb) mds))); auto.
    eapply refines_close.
    eapply adequacy_local_list.
    (* clear initial_mrs_eq_aux WFR MAINM MAINPRE. clear_tac. *)
    clear - WEAKEN.
    clearbody _stb.
    clear _mss _sbtb.
    induction WEAKEN; ss.
    des; subst. rename l into ll. econs; cycle 1.
    { eapply IHf. ss. }

    eapply adequacy_weaken; et.
  Qed.

End CANCEL.
