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


  Lemma stb_find_iff fn
    :
      ((<<NONE: alist_find fn stb = None>>) /\
       (<<FINDMID: alist_find fn (ModSemL.fnsems ms_mid) = None>>) /\
       (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) = None>>)) \/

      (exists md (f: fspecbody),
          (<<SOME: alist_find fn stb = Some (f: fspec)>>) /\
          (<<FINDMID: alist_find fn (ModSemL.fnsems ms_mid) =
                      Some (transl_all
                              (SModSem.mn
                                 (SMod.get_modsem md sk))
                              ∘ fun_to_mid stb (fsb_body f))>>) /\
          (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) =
                      Some (transl_all
                              (SModSem.mn
                                 (SMod.get_modsem md sk))
                              ∘ fun_to_tgt stb f)>>)).
  Proof.
    admit "stb find".
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
    admit "list induction".
  Qed.

  Lemma rsum_update mn mrs frs r
    :
      rsum (update mrs mn r, frs) = rsum (update mrs mn ε, frs) ⋅ r.
  Proof.
    admit "list induction".
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
    ,
      simg (fun '((rs_src, v_src)) '((rs_tgt, v_tgt)) => wf rs_src rs_tgt /\ (v_src: RT) = snd v_tgt /\ (rsum_minus mn (fst rs_tgt)) = fst v_tgt)
           (Ord.from_nat 100%nat)
           (EventsL.interp_Es (ModSemL.prog ms_mid) (transl_all mn (interp_hCallE_mid stb cur i0)) st_src0)
           (EventsL.interp_Es (ModSemL.prog ms_tgt) (transl_all mn (interp_hCallE_tgt stb cur i0 (rsum_minus mn rst))) st_tgt0)
  .
  Proof.
    Opaque subevent.
    ginit.
    { i. eapply cpn6_wcompat; eauto with paco. }
    (* remember (` x : ModSemL.r_state * R <- interp_Es p_src (interp_hCallE_src (trigger ce)) st_src0;; Ret (snd x)) as tmp. *)
    gcofix CIH. i; subst.
    (* intros ? ?. *)
    (* pcofix CIH. i. *)
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

    destruct tbr.
    { des; et. Opaque ord_lt. destruct x4; ss; cycle 1.
      { exfalso. exploit x7; et. }
      steps. esplits; eauto. steps. unshelve esplits; eauto. steps. unfold unwrapU.
      rewrite FINDMID. rewrite FINDTGT. steps.
      guclo ordC_spec. econs.
      { instantiate (2:=(200+200)%ord). rewrite <- OrdArith.add_from_nat. refl. }
      rename f into fs. mred.
      guclo bindC_spec. econs.
      - instantiate (1:= fun '((((mrs_src, frs_src), mps_src), vret_src): (r_state * p_state * Any_src))
                             '((((mrs_tgt, frs_tgt), mps_tgt), vret_tgt): (r_state * p_state * Any_tgt)) =>
                           exists (rret: Σ),
                             (<<ST: (List.length frs_src) = (List.length frs_tgt) /\
                                    frs_src <> [] /\
                                    URA.wf (rsum (mrs_tgt, rret :: frs_tgt))>>) /\
                             (* (<<VAL: vret_src = vret_tgt>>) /\ *)
                             (<<POST: fs.(postcond) x2 vret_src vret_tgt rret>>) /\
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
        { clear - rsum x.
          rewrite rsum_minus_spec. rewrite rsum_minus_spec in *.
          rewrite URA.add_assoc. rewrite <- rsum_update.
          erewrite update_same. rewrite rsum_update.
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
        guclo bindC_spec. econs.
        + gbase. eapply CIH; ss. rr. esplits; ss; et. rewrite URA.unit_idl. clear - WFTGT x.
          rewrite rsum_minus_spec in x. rewrite URA.add_assoc in x.
          rewrite <- rsum_update in x.
          rewrite rsum_cons. rewrite URA.add_comm.
          rewrite rsum_cons. rewrite <- URA.add_assoc.
          rewrite URA.add_comm. rewrite <- URA.add_assoc. auto.
        + ii. ss. des_ifs_safe. des; ss. clarify. destruct p1. des_u.
          steps. esplits; eauto. steps. unfold put. steps. destruct p0; ss. steps.
          unfold handle_rE. destruct r0; ss. destruct l; ss.
          { steps. }
          steps.
          unfold guarantee.
          steps.
          unfold discard.
          steps.
          unfold guarantee. steps. r in SIM. des; ss.
          esplits; ss; eauto.
          { rewrite rsum_minus_spec in x4. rewrite URA.add_assoc in x4.
            rewrite <- rsum_update in x4.
            rewrite rsum_cons. rewrite URA.add_comm.
            rewrite rsum_cons. rewrite <- URA.add_assoc.
            rewrite URA.add_comm. rewrite <- URA.add_assoc. auto.
          }
      - ii. ss. des_ifs_safe. des.
        unfold checkWf, assume; steps. clear_tac. esplits. steps.
        unfold forge; steps. des_ifs; ss. { steps. } steps.
        eexists. instantiate (2:=rret). esplits; et.
        steps. exists (rsum_minus mn (c3, c ⋅ rret :: l1)).
        steps. unshelve esplits; eauto.
        { rewrite rsum_minus_spec. rewrite URA.add_assoc.
          rewrite <- rsum_update. rewrite update_same.
          rewrite rsum_cons in ST1. rewrite rsum_cons in ST1. rewrite rsum_cons in ST1.
          eapply URA.wf_mon. instantiate (1:=c5).
          replace (rsum (c3, l1) ⋅ (c ⋅ rret) ⋅ c5) with (rret ⋅ (c5 ⋅ (c ⋅ rsum (c3, l1)))); auto.
          r_solve.
        }
        steps. unshelve esplits; eauto. steps.
        gbase. eapply CIH; ss.
        rr. esplits; et. { destruct l2; ss. } clear - ST1.
        { eapply URA.wf_mon. instantiate (1:=c5).
          rewrite ! rsum_cons. rewrite ! rsum_cons in ST1.
          replace (c ⋅ rret ⋅ rsum (c3, l1) ⋅ c5) with (rret ⋅ (c5 ⋅ (c ⋅ rsum (c3, l1)))); auto.
          r_solve.
        }
    }


    { des; et. Opaque ord_lt. destruct x4; ss.
      { exfalso. exploit x8; et. ss. }
      steps. esplits; eauto. steps. unshelve esplits; eauto. steps. unfold unwrapU.
      rewrite FINDMID. rewrite FINDTGT. steps.
      guclo ordC_spec. econs.
      { instantiate (1:=(200+200)%ord). rewrite <- OrdArith.add_from_nat. eapply OrdArith.add_refl.

eauto with ord_step. refl. }
      rename f into fs. mred.
      guclo bindC_spec. econs.
      - instantiate (1:= fun '((((mrs_src, frs_src), mps_src), vret_src): (r_state * p_state * Any_src))
                             '((((mrs_tgt, frs_tgt), mps_tgt), vret_tgt): (r_state * p_state * Any_tgt)) =>
                           exists (rret: Σ),
                             (<<ST: (List.length frs_src) = (List.length frs_tgt) /\
                                    frs_src <> [] /\
                                    URA.wf (rsum (mrs_tgt, rret :: frs_tgt))>>) /\
                             (* (<<VAL: vret_src = vret_tgt>>) /\ *)
                             (<<POST: fs.(postcond) x2 vret_src vret_tgt rret>>) /\
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
        { clear - rsum x.
          rewrite rsum_minus_spec. rewrite rsum_minus_spec in *.
          rewrite URA.add_assoc. rewrite <- rsum_update.
          erewrite update_same. rewrite rsum_update.
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
        guclo bindC_spec. econs.
        + gbase. eapply CIH; ss. rr. esplits; ss; et. rewrite URA.unit_idl. clear - WFTGT x.
          rewrite rsum_minus_spec in x. rewrite URA.add_assoc in x.
          rewrite <- rsum_update in x.
          rewrite rsum_cons. rewrite URA.add_comm.
          rewrite rsum_cons. rewrite <- URA.add_assoc.
          rewrite URA.add_comm. rewrite <- URA.add_assoc. auto.
        + ii. ss. des_ifs_safe. des; ss. clarify. destruct p1. des_u.
          steps. esplits; eauto. steps. unfold put. steps. destruct p0; ss. steps.
          unfold handle_rE. destruct r0; ss. destruct l; ss.
          { steps. }
          steps.
          unfold guarantee.
          steps.
          unfold discard.
          steps.
          unfold guarantee. steps. r in SIM. des; ss.
          esplits; ss; eauto.
          { rewrite rsum_minus_spec in x4. rewrite URA.add_assoc in x4.
            rewrite <- rsum_update in x4.
            rewrite rsum_cons. rewrite URA.add_comm.
            rewrite rsum_cons. rewrite <- URA.add_assoc.
            rewrite URA.add_comm. rewrite <- URA.add_assoc. auto.
          }
      - ii. ss. des_ifs_safe. des.
        unfold checkWf, assume; steps. clear_tac. esplits. steps.
        unfold forge; steps. des_ifs; ss. { steps. } steps.
        eexists. instantiate (2:=rret). esplits; et.
        steps. exists (rsum_minus mn (c3, c ⋅ rret :: l1)).
        steps. unshelve esplits; eauto.
        { rewrite rsum_minus_spec. rewrite URA.add_assoc.
          rewrite <- rsum_update. rewrite update_same.
          rewrite rsum_cons in ST1. rewrite rsum_cons in ST1. rewrite rsum_cons in ST1.
          eapply URA.wf_mon. instantiate (1:=c5).
          replace (rsum (c3, l1) ⋅ (c ⋅ rret) ⋅ c5) with (rret ⋅ (c5 ⋅ (c ⋅ rsum (c3, l1)))); auto.
          r_solve.
        }
        steps. unshelve esplits; eauto. steps.
        gbase. eapply CIH; ss.
        rr. esplits; et. { destruct l2; ss. } clear - ST1.
        { eapply URA.wf_mon. instantiate (1:=c5).
          rewrite ! rsum_cons. rewrite ! rsum_cons in ST1.
          replace (c ⋅ rret ⋅ rsum (c3, l1) ⋅ c5) with (rret ⋅ (c5 ⋅ (c ⋅ rsum (c3, l1)))); auto.
          r_solve.
        }
    }



    { des. clear x7. exploit x8; et. i; clarify. clear x8.
      steps. esplits; eauto. steps. esplits; eauto. steps. unfold unwrapU.
      destruct (alist_find fn (ModSemL.fnsems ms_mid)) eqn:FINDFS; cycle 1.
      { steps. }
      destruct (alist_find fn (ModSemL.fnsems ms_tgt)) eqn:FINDFT0; cycle 1.
      { steps.
        apply alist_find_some in FINDFS.
        assert(IN: In fn (List.map fst ms_mid.(ModSemL.fnsems))).
        { rewrite in_map_iff. esplits; et. ss. }
        unfold ms_mid in IN. unfold mds_mid in IN. unfold SMod.to_mid in IN.
        erewrite SMod.transl_fnsems_stable with (tr1:=(fun_to_tgt ∘ _stb)) (mr1:=SModSem.initial_mr) in IN.
        replace (SMod.transl (fun_to_tgt ∘ _stb) SModSem.initial_mr) with (SMod.to_tgt _stb) in IN by refl.
        fold mds_tgt in IN. fold ms_tgt in IN.
        eapply in_map_iff in IN. des; subst. destruct x4. ss.
        eapply alist_find_none in FINDFT0; et.
      }
      mred. des_ifs. mred.
      rename i into i_src.
      rename i0 into i_tgt.
      guclo bindC_spec.
      replace (Ord.from_nat 405) with
          (OrdArith.add (Ord.from_nat 205) (Ord.from_nat 200)); cycle 1.
      { admit "ez". }
      rename f into fs.
      econs.
      - instantiate (1:= fun '((((mrs_src, frs_src), mps_src), vret_src): (r_state * p_state * Any_src))
                             '((((mrs_tgt, frs_tgt), mps_tgt), vret_tgt): (r_state * p_state * Any_tgt)) =>
                           exists (rret: Σ),
                             (<<ST: (List.length frs_src) = (List.length frs_tgt) /\
                                    frs_src <> [] /\
                                    URA.wf (rsum (mrs_tgt, rret :: frs_tgt))>>) /\
                             (* (<<VAL: vret_src = vret_tgt>>) /\ *)
                             (<<POST: fs.(postcond) x2 vret_src vret_tgt rret>>) /\
                             (<<PHYS: mps_src = mps_tgt>>)
                    ).
        apply alist_find_some in FINDFT0.
        apply alist_find_some in FINDFS.
        unfold ms_mid, mds_mid, SMod.to_mid in FINDFS. rewrite SMod.transl_fnsems in FINDFS. unfold SMod.load_fnsems in FINDFS. ss.
        eapply in_flat_map in FINDFS; des. eapply in_flat_map in FINDFS0; des. des_ifs. ss. des; ss. clarify. fold sk in FINDFS0.
        unfold ms_tgt, mds_tgt, SMod.to_tgt in FINDFT0. rewrite SMod.transl_fnsems in FINDFT0. unfold SMod.load_fnsems in FINDFT0. ss.
        eapply in_flat_map in FINDFT0; des. eapply in_flat_map in FINDFT1; des. des_ifs. ss. des; ss. clarify. fold sk in FINDFT1.
        assert(x4 = x7).
        { admit "ez - no function name duplication". }
        subst. rename x7 into md0.
        assert(f = f0).
        { admit "ez - no function name duplication". }
        subst.
        assert(fs = f0).
        { clear - FINDFT0 FINDFS0. admit "ez - no function name duplication". }
        subst.
        fold sk. fold sk. set (mn0:=(SModSem.mn (SMod.get_modsem md0 sk))) in *.
        fold Any_tgt in x5.
        unfold fun_to_src, fun_to_tgt, compose. des_ifs. unfold HoareFun.
        rename x5 into PRECOND. rename x0 into rarg.
        steps. exists (rsum_minus mn0 (update mrs_tgt0 mn c, ε ⋅ rarg :: x1 :: frs_tgt_tl)).
        steps. exists varg_src.
        steps. esplits; et. steps. exists rarg.
        steps. unfold forge, checkWf, assume, guarantee.
        steps. unshelve esplits; eauto.
        unshelve esplits; eauto.
        { clear - rsum x.
          rewrite rsum_minus_spec. rewrite rsum_minus_spec in *.
          rewrite URA.add_assoc. rewrite <- rsum_update.
          erewrite update_same. rewrite rsum_update.
          rewrite rsum_cons.
          replace (x1 ⋅ rsum (update mrs_tgt0 mn ε, frs_tgt_tl) ⋅ c ⋅ (ε ⋅ rarg))
            with (rsum (update mrs_tgt0 mn ε, frs_tgt_tl) ⋅ (c ⋅ (rarg ⋅ x1))); auto.
          r_solve.
        }
        steps. esplits; eauto. steps. unfold cfun. steps. unshelve esplits; eauto. steps.
        unfold fun_to_mid.
        rewrite Any.pair_split. steps.
        rewrite Any.upcast_downcast. steps.
        guclo bindC_spec.
        replace (Ord.from_nat 153) with (OrdArith.add (Ord.from_nat 53) (Ord.from_nat 100)); cycle 1.
        { admit "ez - ordinal nat add". }
        rewrite idK_spec at 1.
        econs.
        + gbase. unfold body_to_tgt, body_to_mid. eapply CIH; ss.
          rr. esplits; ss; et. rewrite URA.unit_idl. clear - WFTGT x.
          rewrite rsum_minus_spec in x. rewrite URA.add_assoc in x.
          rewrite <- rsum_update in x.
          rewrite rsum_cons. rewrite URA.add_comm.
          rewrite rsum_cons. rewrite <- URA.add_assoc.
          rewrite URA.add_comm. rewrite <- URA.add_assoc. auto.
        + ii. ss. des_ifs_safe. des; ss. clarify.
          steps. esplits; eauto. steps. unfold put. steps. destruct p0; ss. steps.
          des_ifs.
          { steps. }
          steps. unfold discard. steps. des. esplits; et.
          rewrite rsum_minus_spec in x4. rewrite URA.add_assoc in x4.
          rewrite <- rsum_update in x4.
          rewrite rsum_cons. rewrite URA.add_comm.
          rewrite rsum_cons. rewrite <- URA.add_assoc.
          rewrite URA.add_comm. rewrite <- URA.add_assoc. auto.
      - ii. ss. des_ifs_safe. des. (* rr in SIM0. des; ss. unfold RelationPairs.RelCompFun in *. ss. *)
        (* r in SIM0. des_ifs. des; ss. *)
        steps. clear_tac. esplits. steps.
        unfold forge, checkWf, assume; steps.
        des_ifs; ss.
        { steps. }
        steps. esplits. steps. instantiate (1:= rret).
        exists (rsum_minus mn (c3, c0 ⋅ rret :: l1)). steps.
        unshelve esplits; eauto.
        { clear - ST1. rewrite rsum_minus_spec.
          rewrite URA.add_assoc. rewrite <- rsum_update.
          rewrite update_same. eapply URA.wf_mon. instantiate (1:=c5).
          rewrite ! rsum_cons in ST1.
          replace (rsum (c3, l1) ⋅ (c0 ⋅ rret) ⋅ c5) with (rret ⋅ (c5 ⋅ (c0 ⋅ rsum (c3, l1)))); auto.
          r_solve.
        }
        steps. unshelve esplits; eauto.
        steps.
        gbase. eapply CIH; ss.
        rr. esplits; et. { destruct l2; ss. } clear - ST1.
        eapply URA.wf_mon. instantiate (1:=c5).
        rewrite ! rsum_cons. rewrite ! rsum_cons in ST1.
        replace (c0 ⋅ rret ⋅ rsum (c3, l1) ⋅ c5) with (rret ⋅ (c5 ⋅ (c0 ⋅ rsum (c3, l1)))); auto.
        r_solve.
    }
  Unshelve.
    all: ss.
    all: try (by apply Ord.O).
    { apply 0. }
  Qed.

  Variable entry_r: Σ.
  Variable mainpre: Any.t -> ord -> Σ -> Prop.
  Variable (mainbody: Any.t -> itree (hCallE +' pE +' eventE) Any.t).
  Hypothesis MAINPRE: mainpre ([]: list val)↑ ord_top entry_r.

  Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)).

  Hypothesis MAINM: In (SMod.main mainpre mainbody) mds.

  Require Import Logic.

  Let MAINF: @alist_find _ _ (@Dec_RelDec string string_Dec) _  "main" stb = Some (mk_simple (fun (_: unit) => (mainpre, fun _ => (⌜True⌝: iProp)%I))).
  Proof.
    unfold stb, _stb.
    rewrite alist_find_map. uo. unfold compose. des_ifs.
    - eapply alist_find_some in Heq. des. des_sumbool. subst. repeat f_equal.
      assert(In ("main", (mk_specbody (mk_simple (fun (_: unit) => (mainpre, fun _ => (⌜True⌝: iProp)%I))) mainbody)) sbtb).
      { unfold sbtb, _sbtb, mss, _mss. eapply in_flat_map. esplits; et.
        { rewrite in_map_iff. esplits; et. }
        ss. et.
      }
      admit "ez - uniqueness of fname".
    - eapply alist_find_none in Heq.
      { exfalso. eapply Heq.
        unfold sbtb, _sbtb, mss, _mss. eapply in_flat_map. esplits; et.
        { rewrite in_map_iff. esplits; et. }
        ss. et.
      }
  Qed.

  Let initial_r_state ms entry_r: r_state :=
    (fun mn => match alist_find mn ms.(ModSemL.initial_mrs) with
               | Some r => fst r
               | None => ε
               end, [entry_r]). (*** we have a dummy-stack here ***)

  Opaque EventsL.interp_Es.

  Require Import ProofMode.

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

  Theorem adequacy_type_t2m: Beh.of_program (ModL.compile (Mod.add_list mds_tgt)) <1=
                             Beh.of_program (ModL.compile_arg (Mod.add_list mds_mid) (Any.pair ord_top↑ ([]: list val)↑)).
  Proof.
    eapply adequacy_global_itree.
    exists (Ord.from_nat 100%nat). ss.
    ginit.
    { eapply cpn6_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr, ModSemL.initial_itr_arg. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.
    unfold assume.
    steps. unfold ModL.wf in *. des.
    esplits; et.
    { inv WF. econs.
      { rewrite fns_eq. auto. }
      { pose proof fst_initial_mrs_eq. unfold ms_tgt, ms_mid in H.
        rewrite H. auto. }
    }
    { rewrite sk_eq. auto. }
    steps. folder.
    set (st_mid0 := ((ModSemL.initial_r_state ms_mid), (ModSemL.initial_p_state ms_mid))).
    set (st_midr0 := ((initial_r_state ms_mid ε), (ModSemL.initial_p_state ms_mid))).
    set (st_tgtl0 := ((initial_r_state ms_tgt entry_r), (ModSemL.initial_p_state ms_tgt))).
    set (st_tgt0 := (ModSemL.initial_r_state ms_tgt, (ModSemL.initial_p_state ms_tgt))).
    (* Local Opaque URA.add. *)
    assert(SIM: wf st_midr0 st_tgtl0).
    { r. ss. esplits; ss; et.
      { admit "resourve wf". }
      rewrite initial_p_eq. auto.
    }
    unfold mrec.

    hexploit (stb_find_iff "main"). i. des; clarify. destruct f. ss. subst.
    Local Transparent ModSemL.prog. ss.
    rewrite FINDTGT. rewrite FINDMID. steps.
    unfold fun_to_mid, fun_to_tgt. ss.
    unfold HoareFun. steps.

    unfold forge, put, checkWf, discard.
    eexists. steps. eexists. steps. exists tt. steps.
    eexists. steps. unshelve esplits.
    { admit "resource wf". }
    steps. exists ord_top. steps. unshelve esplits.
    { red. uipropall. esplits; et. r. uipropall. }
    steps. rewrite Any.pair_split. steps.
    rewrite Any.upcast_downcast. steps.

    guclo ordC_spec. econs.
    { instantiate (2:=(_ + _)%ord).
      rewrite <- OrdArith.add_from_nat.
      eapply OrdArith.le_from_nat. refl. }
    {
      guclo bindC_spec. econs.
      { gfinal. right. fold simg.
        eapply adequacy_type_aux; ss. splits; ss.
        { admit "initial_r_state wf". }
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
