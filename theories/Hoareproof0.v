Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef.
Require Import SimSTS.
Require Import SimGlobal.
From Ordinal Require Import Ordinal Arithmetic.
Require Import Red IRed.

Set Implicit Arguments.




















Section CANCEL.

  (*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
  Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)



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

  (* Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) sk) mds). *)
  (* Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss). *)
  (* Let stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb. *)

  Let mds_mid: list Mod.t := List.map (SMod.to_mid stb) mds.
  Let mds_tgt: list Mod.t := List.map (SMod.to_tgt _stb) mds.

  Let ms_mid: ModSemL.t := ModL.enclose (Mod.add_list mds_mid).
  Let ms_tgt: ModSemL.t := ModL.enclose (Mod.add_list mds_tgt).


  Lemma sk_eq:
    ModL.sk (Mod.add_list mds_tgt) = ModL.sk (Mod.add_list mds_mid).
  Proof.
    unfold ms_tgt, ms_mid, mds_mid, mds_tgt, ModL.enclose.
    rewrite ! Mod.add_list_sk. f_equal.
    generalize mds. clear. i. induction mds0; ss.
    rewrite IHmds0. auto.
  Qed.

  Lemma fst_initial_mrs_eq:
    List.map fst (ModSemL.initial_mrs ms_tgt) = List.map fst (ModSemL.initial_mrs ms_mid).
  Proof.
    pose proof sk_eq.
    unfold ms_tgt, ms_mid, mds_tgt, mds_mid, ModL.enclose.
    unfold mds_mid, mds_tgt in H. rewrite H.
    generalize (ModL.sk (Mod.add_list (List.map (SMod.to_mid stb) mds))). i.
    rewrite ! Mod.add_list_initial_mrs.
    generalize mds. clear. i. induction mds0; auto.
    ss. rewrite IHmds0. auto.
  Qed.

  Lemma initial_p_eq:
    ModSemL.initial_p_state ms_tgt = ModSemL.initial_p_state ms_mid.
  Proof.
    unfold ModSemL.initial_p_state. extensionality mn.
    pose proof sk_eq.
    unfold ms_tgt, ms_mid, mds_tgt, mds_mid, ModL.enclose.
    unfold mds_mid, mds_tgt in H. rewrite H.
    generalize (ModL.sk (Mod.add_list (List.map (SMod.to_mid stb) mds))). i.
    rewrite ! Mod.add_list_initial_mrs.
    generalize mds. clear. i. induction mds0; auto.
    ss. rewrite eq_rel_dec_correct in *. des_ifs.
  Qed.

  Lemma fns_eq:
    (List.map fst (ModSemL.fnsems (ModL.enclose (Mod.add_list mds_tgt))))
    =
    (List.map fst (ModSemL.fnsems (ModL.enclose (Mod.add_list mds_mid)))).
  Proof.
    pose proof sk_eq. unfold ModL.enclose.
    unfold mds_mid, mds_tgt, ModL.enclose.
    unfold mds_mid, mds_tgt in H. rewrite H.
    generalize (ModL.sk (Mod.add_list (List.map (SMod.to_mid stb) mds))). i.
    rewrite ! Mod.add_list_fns. rewrite ! List.map_map. f_equal.
    f_equal. extensionality sm. ss. rewrite ! List.map_map. f_equal.
    extensionality fnsb. destruct fnsb as [fn sb]. ss.
  Qed.

  Lemma stb_find_iff fn
    :
      ((<<NONE: alist_find fn stb = None>>) /\
       (<<FINDMID: alist_find fn (ModSemL.fnsems ms_mid) = None>>) /\
       (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) = None>>)) \/

      (exists md (f: fspecbody),
          (<<SOME: alist_find fn stb = Some (f: fspec)>>) /\
          (<<SBTB: alist_find fn sbtb = Some f>>) /\
          (<<FINDMID: alist_find fn (ModSemL.fnsems ms_mid) =
                      Some (transl_all (T:=_)
                              (SModSem.mn (SMod.get_modsem md sk))
                              ∘ fun_to_mid stb (fsb_body f))>>) /\
          (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) =
                      Some (transl_all (T:=_)
                              (SModSem.mn (SMod.get_modsem md sk))
                              ∘ fun_to_tgt (SModSem.mn (SMod.get_modsem md sk)) stb f)>>) /\
          (<<MIN: List.In (SModSem.mn (SMod.get_modsem md sk)) (List.map fst ms_tgt.(ModSemL.initial_mrs))>>)).
  Proof.
    unfold ms_mid, ms_tgt, mds_tgt, mds_mid, SMod.to_mid, mds_tgt, SMod.to_tgt.
    rewrite SMod.transl_fnsems. rewrite SMod.transl_fnsems. rewrite SMod.transl_initial_mrs. fold sk.
    unfold stb at 1 3, _stb at 1 3. unfold sbtb, _sbtb, _mss. rewrite alist_find_map.
    generalize mds. induction mds0; ss; auto. rewrite ! alist_find_app_o.
    erewrite ! SMod.red_do_ret2. rewrite ! alist_find_map. uo.
    destruct (alist_find fn (SModSem.fnsems (SMod.get_modsem a sk))) eqn:FIND.
    { right. esplits; et. }
    des.
    { left. esplits; et. }
    { right. esplits; et. }
  Qed.

  Let W: Type := (r_state * p_state).
  Let rsum: r_state -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (fold_left (⋅) (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) ⋅ (fold_left (⋅) frs_tgt ε).

  Let rsum_minus (mn: mname): r_state -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (fold_left (⋅) (List.map ((update mrs_tgt mn ε) <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) ⋅ (fold_left (⋅) (tl frs_tgt) ε).



  Lemma fold_left_radd (r0 r1: Σ) rl
    :
      fold_left URA.add rl (r0 ⋅ r1) = r0 ⋅ fold_left URA.add rl r1.
  Proof.
    revert r0 r1. induction rl; ss.
    i. rewrite <- URA.add_assoc. rewrite IHrl. auto.
  Qed.

  Lemma rsum_minus_spec mn mrs fhd ftl
    :
      rsum_minus mn (mrs, fhd::ftl) = rsum (update mrs mn ε, ftl).
  Proof.
    unfold rsum_minus, rsum. ss.
  Qed.

  Lemma fold_left_add (r: Σ) rs
    :
      fold_left URA.add rs r = (fold_left URA.add rs ε) ⋅ r.
  Proof.
    revert r. induction rs; ss.
    { i. rewrite URA.unit_idl. auto. }
    i. rewrite IHrs. rewrite (IHrs (ε ⋅ a)). r_solve.
  Qed.

  Lemma rsum_update mn mrs frs r
        (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (IN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      rsum (update mrs mn r, frs) = rsum (update mrs mn ε, frs) ⋅ r.
  Proof.
    unfold rsum. rewrite <- URA.add_assoc. rewrite (URA.add_comm _ r).
    rewrite URA.add_assoc. f_equal. unfold compose.
    rewrite <- (List.map_map fst). rewrite <- (List.map_map fst). revert IN NODUP.
    generalize (List.map fst (ModSemL.initial_mrs ms_tgt)) as mds0. i.
    cut (forall r0 r1, fold_left URA.add (List.map (update mrs mn r0) mds0) ε ⋅ r1
                       =
                       fold_left URA.add (List.map (update mrs mn r1) mds0) ε ⋅ r0).
    { i. specialize (H r ε). rewrite URA.unit_id in H. auto. }
    i. revert mn r0 r1 IN NODUP. induction mds0; ss. i.
    destruct (classic (In mn mds0)).
    { clear IN. rewrite (fold_left_add (ε ⋅ update mrs mn r0 a)).
      rewrite (fold_left_add (ε ⋅ update mrs mn r1 a)).
      rewrite ! URA.unit_idl. rewrite <- URA.add_assoc. rewrite <- URA.add_assoc.
      rewrite (URA.add_comm _ r1). rewrite (URA.add_comm _ r0).
      rewrite URA.add_assoc. rewrite URA.add_assoc.
      inv NODUP. rewrite IHmds0; ss.
      f_equal. unfold update. des_ifs.
    }
    { des; ss. rewrite (fold_left_add (ε ⋅ update mrs mn r0 a)).
      rewrite (fold_left_add (ε ⋅ update mrs mn r1 a)). subst.
      unfold update at 2 4. des_ifs.
      rewrite ! URA.unit_idl. rewrite <- URA.add_assoc. rewrite <- URA.add_assoc. f_equal.
      { revert H. clear IHmds0 NODUP. induction mds0; ss. i.
        rewrite (fold_left_add (ε ⋅ update mrs mn r0 a)).
        rewrite (fold_left_add (ε ⋅ update mrs mn r1 a)).
        rewrite IHmds0; auto. f_equal. f_equal.
        unfold update. des_ifs; ss. exfalso. eapply H; auto.
      }
      { eapply URA.add_comm. }
    }
  Qed.

  Lemma update_same A (mrs: string -> A) mn
    :
      update mrs mn (mrs mn) = mrs.
  Proof.
    extensionality mn0. unfold update. des_ifs.
  Qed.

  Lemma rsum_cons mrs fhd ftl
    :
      rsum (mrs, fhd::ftl) = fhd ⋅ rsum (mrs, ftl).
  Proof.
    ss. transitivity (fold_left URA.add (List.map (mrs <*> fst) (ModSemL.initial_mrs ms_tgt)) ε
                                ⋅ (fhd ⋅ fold_left URA.add ftl ε)).
    { f_equal.
      generalize fhd. generalize (@URA.unit (GRA.to_URA Σ)).
      induction ftl; ss.
      { i. r_solve. }
      { i. ss.
        replace (c ⋅ fhd0 ⋅ a) with ((c ⋅ a) ⋅ fhd0) by r_solve.
        rewrite IHftl. r_solve.
      }
    }
    { r_solve. }
  Qed.

  Let wf: W -> W -> Prop :=
    fun '((mrs_src, frs_src), mps_src) '((mrs_tgt, frs_tgt), mps_tgt) =>
      (<<LEN: List.length frs_src = List.length frs_tgt>>) /\
      (<<NNIL: frs_src <> []>>) /\
      (<<WFTGT: URA.wf (rsum (mrs_tgt, frs_tgt))>>) /\
      (<<PHYS: mps_src = mps_tgt>>)
  .
  Local Opaque rsum rsum_minus.

  Let WF0: List.map fst sbtb = List.map fst stb.
  Proof. unfold stb, _stb. rewrite List.map_map. apply List.map_ext. i. des_ifs. Qed.



  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac mred := repeat (cbn; ired_both).

  Ltac steps := repeat (mred; try _step; des_ifs_safe).





  (*** TODO: move to ITreelib ***)
  (*** it inserts "subevent" ***)
  (* Lemma bind_trigger: *)
  (*   forall [E : Type -> Type] [R U : Type] (e : E U) (k : U -> itree E R), ` x : U <- trigger e;; k x = Vis e (fun x : U => k x). *)
  (* Proof. i. eapply bind_trigger. Qed. *)

  Let adequacy_type_aux:
    forall RT
           st_src0 st_tgt0 (SIM: wf st_src0 st_tgt0) (i0: itree (hCallE +' pE +' eventE) RT)
           mn cur
           rst (EQ: rst = fst st_tgt0)
           (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
           (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    ,
      simg (fun '((rs_src, v_src)) '((rs_tgt, v_tgt)) => wf rs_src rs_tgt /\ (v_src: RT) = snd v_tgt /\ (rsum_minus mn (fst rs_tgt)) = fst v_tgt)
           (Ord.from_nat 100%nat)
           (EventsL.interp_Es (ModSemL.prog ms_mid) (transl_all mn (interp_hCallE_mid stb cur i0)) st_src0)
           (EventsL.interp_Es (ModSemL.prog ms_tgt) (transl_all mn (interp_hCallE_tgt mn stb cur i0 (rsum_minus mn rst))) st_tgt0)
  .
  Proof.
    Opaque subevent.
    ginit.
    { i. eapply cpn6_wcompat; eauto with paco. }
    gcofix CIH. i; subst.
    ides i0; try rewrite ! unfold_interp; cbn; mred.
    { steps. }
    { steps. gbase. eapply CIH; [..|M]; Mskip et. ss. }
    destruct e; cycle 1.
    {
      destruct s; ss.
      {
        destruct st_src0 as [rst_src0 pst_src0], st_tgt0 as [rst_tgt0 pst_tgt0]; ss. des_ifs. des; clarify.
        destruct p; ss.
        - rewrite <- bind_trigger. resub. steps. gbase. eapply CIH; ss.
        - rewrite <- bind_trigger. resub. steps. gbase. eapply CIH; ss.
      }
      { dependent destruction e.
        - rewrite <- bind_trigger. resub. steps. esplits; eauto. steps. gbase. eapply CIH; [..|M]; Mskip et. ss.
        - rewrite <- bind_trigger. resub. steps. esplits; eauto. steps. gbase. eapply CIH; [..|M]; Mskip et. ss.
        - rewrite <- bind_trigger. resub. steps. gbase. eapply CIH; [..|M]; Mskip et. ss.
      }
    }
    dependent destruction h.
    rewrite <- bind_trigger. resub.
    set (ModSemL.prog ms_mid) as p_mid in *.
    set (ModSemL.prog ms_tgt) as p_tgt in *.
    ss.
    seal_left.

    steps. hexploit (stb_find_iff fn). i. des.
    { rewrite NONE. steps. }
    unfold HoareCall, put, guarantee, discard.

    destruct st_tgt0 as [rst_tgt0 pst_tgt0]. destruct st_src0 as [rst_src0 pst_src0].
    destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]] eqn:T; ss. steps.
    { rr in SIM. des_ifs_safe. des; ss. destruct l; ss. }

    (*** exploiting both_tau ***)
    rewrite SOME. ss. mred. force_r.
    unseal_left. ired_both. rewrite SOME. steps.

    match goal with
    | |- _ ?i_tgt => replace i_tgt with (Ret tt;;; i_tgt)
    end.
    2: { mred. auto. }
    guclo ordC_spec. econs.
    { instantiate (2:=(400+5)%ord).
      rewrite <- OrdArith.add_from_nat. refl. }
    guclo bindC_spec. econs.
    { instantiate (1:= fun '(st_src, o) (_: unit) => st_src = (c, l, pst_src0) /\ o = x4).
      destruct tbr.
      { steps. des. destruct x4; ss.
        { exists n. steps. }
        { exfalso. hexploit x7; ss. }
      }
      { steps. des. splits; auto. symmetry. auto. }
    }
    i. destruct vret_src, vret_tgt. des; subst.

    steps. esplits; eauto. steps. unshelve esplits; eauto. steps. unfold unwrapU.
    rewrite FINDMID. rewrite FINDTGT. rewrite ! bind_ret_l.

    Local Opaque fun_to_mid fun_to_tgt.
    rewrite Any.pair_split. cbn. rewrite ! bind_ret_l.
    rewrite Any.upcast_downcast. cbn. rewrite ! bind_ret_l.
    rewrite Any.pair_split. cbn. rewrite ! bind_ret_l.
    rewrite Any.upcast_downcast. cbn. rewrite ! bind_ret_l.
    steps.
    Local Transparent fun_to_mid fun_to_tgt.

    guclo ordC_spec. econs.
    { instantiate (1:=(192+200)%ord). rewrite <- OrdArith.add_from_nat. refl. }
    rename f into fs.
    guclo bindC_spec. econs.

    { instantiate (1:= fun '((((mrs_src, frs_src), mps_src), vret_src): (r_state * p_state * Any_src))
                           '((((mrs_tgt, frs_tgt), mps_tgt), vret_tgt): (r_state * p_state * Any_tgt)) =>
                         exists (rret: Σ),
                           (<<ST: (List.length frs_src) = (List.length frs_tgt) /\
                                  frs_src <> [] /\
                                  URA.wf (rsum (mrs_tgt, rret :: frs_tgt))>>) /\
                           (<<POST: fs.(postcond) mn x2 vret_src vret_tgt rret>>) /\
                           (<<PHYS: mps_src = mps_tgt>>)
                  ).
      fold sk. fold sk. set (mn0:=SModSem.mn (SMod.get_modsem md sk)) in *.
      fold Any_tgt in x5.
      unfold fun_to_src, fun_to_tgt, compose. des_ifs. unfold HoareFun.
      rename x5 into PRECOND. rename x0 into rarg.
      steps. exists (rsum_minus mn0 (update mrs_tgt0 mn c0, ε ⋅ rarg :: x1 :: frs_tgt_tl)).
      steps. exists varg_src.
      steps. esplits; et. steps. exists rarg.
      steps. unfold forge, checkWf, assume, guarantee.
      steps.
      unshelve esplits; eauto.
      { clear - rsum x MIN MIN0 NODUP.
        rewrite rsum_minus_spec; auto. rewrite rsum_minus_spec in *; auto.
        rewrite URA.add_assoc. rewrite <- rsum_update; auto.
        erewrite update_same. rewrite rsum_update; auto.
        rewrite rsum_cons.
        replace (x1 ⋅ rsum (update mrs_tgt0 mn ε, frs_tgt_tl) ⋅ c0 ⋅ (ε ⋅ rarg))
          with (rsum (update mrs_tgt0 mn ε, frs_tgt_tl) ⋅ (c0 ⋅ (rarg ⋅ x1))); auto.
        r_solve.
      }
      steps. esplits; eauto. steps. unshelve esplits; eauto. steps.
      unfold fun_to_mid.
      rewrite Any.pair_split. ss. steps.
      rewrite Any.upcast_downcast. steps.
      guclo ordC_spec. econs.
      { instantiate (1:=(53+100)%ord). rewrite <- OrdArith.add_from_nat. refl. }
      rewrite idK_spec at 1.
      guclo bindC_spec. econs.
      { gbase. eapply CIH; ss. rr. esplits; ss; et. rewrite URA.unit_idl. clear - WFTGT x MIN MIN0 NODUP.
        rewrite rsum_minus_spec in x; auto. rewrite URA.add_assoc in x.
        rewrite <- rsum_update in x; auto.
        rewrite rsum_cons. rewrite URA.add_comm.
        rewrite rsum_cons. rewrite <- URA.add_assoc.
        rewrite URA.add_comm. rewrite <- URA.add_assoc. auto. }
      { ii. ss. des_ifs_safe. des; ss. clarify. destruct p, p0.
        steps. esplits; eauto. steps. unfold put. steps. steps.
        unfold handle_rE. destruct r0; ss. destruct l; ss.
        { steps. }
        steps.
        unfold guarantee.
        steps.
        unfold discard.
        steps. des. clarify.
        esplits; ss; eauto.
        { rewrite rsum_minus_spec in x5; auto. rewrite URA.add_assoc in x5.
          rewrite <- rsum_update in x5; auto.
          rewrite rsum_cons. rewrite URA.add_comm.
          rewrite rsum_cons. rewrite <- URA.add_assoc.
          rewrite URA.add_comm. rewrite <- URA.add_assoc. auto.
        }
      }
    }
    { ii. ss. des_ifs_safe. des.
      steps. esplits. steps.
      unfold forge, checkWf, assume; steps.
      des_ifs; ss.
      { steps. }
      steps. esplits. steps. instantiate (1:= rret).
      exists (rsum_minus mn (c3, c6 ⋅ rret :: l1)). steps.
      unshelve esplits; eauto.
      { clear - ST1 MIN MIN0 NODUP. rewrite rsum_minus_spec; auto.
        rewrite URA.add_assoc. rewrite <- rsum_update; auto.
        rewrite update_same. eapply URA.wf_mon. instantiate (1:=c5).
        rewrite ! rsum_cons in ST1.
        replace (rsum (c3, l1) ⋅ (c6 ⋅ rret) ⋅ c5) with (rret ⋅ (c5 ⋅ (c6 ⋅ rsum (c3, l1)))); auto.
        r_solve.
      }
      steps. unshelve esplits; eauto.
      steps.
      gbase. eapply CIH; ss.
      rr. esplits; et. { destruct l2; ss. } clear - ST1.
      eapply URA.wf_mon. instantiate (1:=c5).
      rewrite ! rsum_cons. rewrite ! rsum_cons in ST1.
      replace (c6 ⋅ rret ⋅ rsum (c3, l1) ⋅ c5) with (rret ⋅ (c5 ⋅ (c6 ⋅ rsum (c3, l1)))); auto.
      r_solve.
    }
  Unshelve.
    all: try (by apply Ord.O).
  Qed.

  Variable entry_r: Σ.
  Variable mainpre: Any.t -> ord -> Σ -> Prop.
  Variable (mainbody: (mname * Any.t) -> itree (hCallE +' pE +' eventE) Any.t).
  Hypothesis MAINPRE: mainpre ([]: list val)↑ ord_top entry_r.

  Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)).

  Require Import Logic.

  Hypothesis MAINM: alist_find "main" sbtb = Some (mk_specbody (mk_simple (fun _ : () => (mainpre, fun _ => (⌜True⌝: iProp)%I))) mainbody).

  Let initial_r_state ms entry_r: r_state :=
    (fun mn => match alist_find mn ms.(ModSemL.initial_mrs) with
               | Some r => fst r
               | None => ε
               end, [entry_r]). (*** we have a dummy-stack here ***)

  Opaque EventsL.interp_Es.

  Theorem adequacy_type_t2m: Beh.of_program (ModL.compile (Mod.add_list mds_tgt)) <1=
                             Beh.of_program (ModL.compile_arg (Mod.add_list mds_mid) (Any.pair ""↑ (Any.pair ord_top↑ ([]: list val)↑))).
  Proof.
    assert (IWF: URA.wf (entry_r ⋅ rsum (fun mn => match alist_find mn (ModSemL.initial_mrs ms_tgt) with
                                                   | Some r => fst r
                                                   | None => ε
                                                   end, []))).
    { clear - WFR. unfold ModSemL.initial_r_state in WFR.
      rewrite ! rsum_cons in WFR. rewrite ! URA.unit_idl in WFR. auto. }
    eapply adequacy_global_itree.
    exists (Ord.from_nat 100%nat). ss.
    ginit.
    { eapply cpn6_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr, ModSemL.initial_itr_arg. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.
    unfold assume.
    steps. unfold ModL.wf in *. des.
    assert (NODUP: List.NoDup (map fst ms_tgt.(ModSemL.initial_mrs))).
    { inv WF. rewrite fst_initial_mrs_eq. unfold ms_mid. auto. }
    esplits; et.
    { inv WF. econs; auto. rewrite fns_eq. auto. }
    { rewrite sk_eq. auto. }
    steps. folder.
    set (st_mid0 := ((ModSemL.initial_r_state ms_mid), (ModSemL.initial_p_state ms_mid))).
    set (st_midr0 := ((initial_r_state ms_mid ε), (ModSemL.initial_p_state ms_mid))).
    set (st_tgtl0 := ((initial_r_state ms_tgt entry_r), (ModSemL.initial_p_state ms_tgt))).
    set (st_tgt0 := (ModSemL.initial_r_state ms_tgt, (ModSemL.initial_p_state ms_tgt))).
    assert(SIM: wf st_midr0 st_tgtl0).
    { r. ss. esplits; ss; et.
      { rewrite rsum_cons. auto. }
      rewrite initial_p_eq. auto. }
    unfold mrec.

    hexploit (stb_find_iff "main"). i. des; clarify.
    { clear - NONE MAINM. unfold stb, _stb in NONE.
      rewrite alist_find_map in NONE. uo.
      unfold sbtb in MAINM. rewrite MAINM in NONE. ss. }

    Local Transparent ModSemL.prog. ss.
    rewrite FINDTGT. rewrite FINDMID. steps.
    unfold fun_to_mid, fun_to_tgt. ss.
    unfold HoareFun. steps.

    unfold forge, put, checkWf, discard.
    rewrite Any.pair_split. steps.
    rewrite Any.upcast_downcast. steps.
    rewrite Any.pair_split. steps.
    rewrite Any.upcast_downcast. steps.
    rewrite Any.pair_split. steps.
    rewrite Any.upcast_downcast. steps.

    eexists. steps. eexists. steps. exists tt. steps.
    eexists. steps.

    unshelve esplits.
    { instantiate (1:=entry_r).
      instantiate (1:=rsum_minus (SModSem.mn (SMod.get_modsem md sk))
                                 (fun mn => match alist_find mn (ModSemL.initial_mrs ms_tgt) with
                                            | Some r => r.1
                                            | None => ε
                                            end, [ε ⋅ entry_r; ε])).
      clear - WFR MIN NODUP. rewrite URA.unit_idl. rewrite URA.add_assoc.
      rewrite rsum_minus_spec; auto. unfold ModSemL.initial_r_state in WFR.
      erewrite <- rsum_update; auto. erewrite update_same. rewrite ! rsum_cons in *.
      match goal with
      | H: URA.wf ?r0 |- URA.wf ?r1 => replace r1 with r0; [apply H|r_solve]
      end.
    }
    steps. exists ord_top. steps. unshelve esplits.
    { red. uipropall. esplits; et. r. uipropall. }
    steps.

    guclo ordC_spec. econs.
    { instantiate (2:=(_ + _)%ord).
      rewrite <- OrdArith.add_from_nat.
      eapply OrdArith.le_from_nat. refl. }
    {
      guclo bindC_spec. econs.
      { gfinal. right. fold simg.
        eapply adequacy_type_aux; ss. splits; ss.
        { rewrite ! rsum_cons. rewrite ! URA.unit_idl. auto. }
        { rewrite initial_p_eq. auto. }
      }
      i. ss.
      destruct vret_src as [[[mrs_src fr_src] mps_src] v_src].
      destruct vret_tgt as [[[mrs_tgt fr_tgt] mps_tgt] [r_tgt v_tgt]].
      ss. des; subst. steps.
      destruct fr_tgt; ss.
      { steps. }
      steps. red in x2. uipropall. des. red in x4. uipropall.
    }
    Unshelve.
    all: try (by apply Ord.O).
    all: try (by apply 0%nat).
  Qed.

End CANCEL.
