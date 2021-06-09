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


















  (* Ltac ired_l := *)
  (*   cbn; *)
  (*   match goal with *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ (_ >>= _ >>= _) _) ] => *)
  (*     prw ltac:(rrw bind_bind _continue) 2 0 *)
  (*     (* apply simg_l_bind_bind; ired_l *) *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ ((tau;; _) >>= _) _) ] => *)
  (*     apply simg_l_bind_tau *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ ((Ret _) >>= _) _) ] => *)
  (*     apply simg_l_bind_ret_l; ired_l *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ (trigger _) _) ] => *)
  (*     apply simg_l_trigger_ret_rev *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ (interp _ _) _) ] => *)
  (*     ((interp_red; ired_l) || idtac) *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ ((interp _ _) >>= _) _) ] => *)
  (*     ((interp_red; ired_l) || idtac) *)

  (*   (**************************** interp_Es ******************************) *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ (interp_Es _ (_ >>= _) _) _) ] => *)
  (*     apply simg_l_interp_Es_bind; ired_l *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ (interp_Es _ (tau;; _) _) _) ] => *)
  (*     apply simg_l_interp_Es_tau *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ (interp_Es _ (Ret _) _) _) ] => *)
  (*     apply simg_l_interp_Es_ret *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ (interp_Es _ (trigger ?e) _) _) ] => *)
  (*     match (type of e) with *)
  (*     | context[rE] => apply simg_l_interp_Es_rE *)
  (*     | context[eventE] => apply simg_l_interp_Es_eventE *)
  (*     | context[pE] => apply simg_l_interp_Es_pE *)
  (*     | context[callE] => apply simg_l_interp_Es_callE *)
  (*     | _ => fail 2 *)
  (*     end *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ (interp_Es _ triggerNB _) _) ] => *)
  (*     apply simg_l_interp_Es_triggerNB *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ (interp_Es _ triggerUB _) _) ] => *)
  (*     apply simg_l_interp_Es_triggerUB *)

  (*   (**************************** interp_Es2 ******************************) *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ ((interp_Es _ (_ >>= _) _) >>= _) _) ] => *)
  (*     apply simg_l_interp_Es_bind2; ired_l *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ ((interp_Es _ (tau;; _) _) >>= _) _) ] => *)
  (*     apply simg_l_interp_Es_tau2 *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ ((interp_Es _ (Ret _) _) >>= _) _) ] => *)
  (*     apply simg_l_interp_Es_ret2; ired_l *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ ((interp_Es _ (trigger ?e) _) >>= _) _) ] => *)
  (*     match (type of e) with *)
  (*     | context[rE] => apply simg_l_interp_Es_rE2 *)
  (*     | context[eventE] => apply simg_l_interp_Es_eventE2 *)
  (*     | context[pE] => apply simg_l_interp_Es_pE2 *)
  (*     | context[callE] => apply simg_l_interp_Es_callE2 *)
  (*     | _ => fail 2 *)
  (*     end *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ ((interp_Es _ triggerNB _) >>= _) _) ] => *)
  (*     apply simg_l_interp_Es_triggerNB2 *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ ((interp_Es _ triggerUB _) >>= _) _) ] => *)
  (*     apply simg_l_interp_Es_triggerUB2 *)

  (*   | _ => idtac *)
  (*   end. *)

  (* Ltac ired_r := *)
  (*   cbn; *)
  (*   match goal with *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ (_ >>= _ >>= _)) ] => *)
  (*     apply simg_r_bind_bind; ired_r *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ ((tau;; _) >>= _)) ] => *)
  (*     apply simg_r_bind_tau *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ ((Ret _) >>= _)) ] => *)
  (*     apply simg_r_bind_ret_l; ired_r *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ (trigger _)) ] => *)
  (*     apply simg_r_trigger_ret_rev *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ (interp _ _)) ] => *)
  (*     ((interp_red; ired_r) || idtac) *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ ((interp _ _) >>= _)) ] => *)
  (*     ((interp_red; ired_r) || idtac) *)

  (*   (**************************** interp_Es ******************************) *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ (interp_Es _ (_ >>= _) _)) ] => *)
  (*     apply simg_r_interp_Es_bind; ired_l *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ (interp_Es _ (tau;; _) _)) ] => *)
  (*     apply simg_r_interp_Es_tau *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ (interp_Es _ (Ret _) _)) ] => *)
  (*     apply simg_r_interp_Es_ret *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ (interp_Es _ (trigger ?e) _)) ] => *)
  (*     match (type of e) with *)
  (*     | context[rE] => apply simg_r_interp_Es_rE *)
  (*     | context[eventE] => apply simg_r_interp_Es_eventE *)
  (*     | context[pE] => apply simg_r_interp_Es_pE *)
  (*     | context[callE] => apply simg_r_interp_Es_callE *)
  (*     | _ => fail 2 *)
  (*     end *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ (interp_Es _ triggerNB _)) ] => *)
  (*     apply simg_r_interp_Es_triggerNB *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ (interp_Es _ triggerUB _)) ] => *)
  (*     apply simg_r_interp_Es_triggerUB *)

  (*   (**************************** interp_Es2 ******************************) *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ ((interp_Es _ (_ >>= _) _) >>= _)) ] => *)
  (*     apply simg_r_interp_Es_bind2; ired_l *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ ((interp_Es _ (tau;; _) _) >>= _)) ] => *)
  (*     apply simg_r_interp_Es_tau2 *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ ((interp_Es _ (Ret _) _) >>= _)) ] => *)
  (*     apply simg_r_interp_Es_ret2; ired_l *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ ((interp_Es _ (trigger ?e) _) >>= _)) ] => *)
  (*     match (type of e) with *)
  (*     | context[rE] => apply simg_r_interp_Es_rE2 *)
  (*     | context[eventE] => apply simg_r_interp_Es_eventE2 *)
  (*     | context[pE] => apply simg_r_interp_Es_pE2 *)
  (*     | context[callE] => apply simg_r_interp_Es_callE2 *)
  (*     | _ => fail 2 *)
  (*     end *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ ((interp_Es _ triggerNB _) >>= _)) ] => *)
  (*     apply simg_r_interp_Es_triggerNB2 *)
  (*   | [ |- (gpaco5 _simg _ _ _ _ _ _ _ ((interp_Es _ triggerUB _) >>= _)) ] => *)
  (*     apply simg_r_interp_Es_triggerUB2 *)

  (*   | _ => idtac *)
  (*   end. *)

  (* Ltac ired_all := ired_l; ired_r. *)





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

  Let sk: Sk.t := fold_right Sk.add Sk.unit (List.map SMod.sk mds).
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





  Lemma embed_l
        (E1 E2: Type -> Type)
        T (e: E1 T)
    :
      trigger (e|)%sum = (trigger e: itree (E1 +' E2) T)
  .
  Proof. refl. Qed.

  Lemma embed_r
        (E1 E2: Type -> Type)
        T (e: E2 T)
    :
      trigger (|e)%sum = (trigger e: itree (E1 +' E2) T)
  .
  Proof. refl. Qed.

  Lemma embed_l_gen
        (E1 E2: Type -> Type)
        `{E1 -< E}
        `{E2 -< E}
        T (e: E1 T)
    :
      trigger (e|)%sum = (trigger e: itree E T)
  .
  Proof. refl. Qed.

  Lemma embed_r_gen
        (E1 E2: Type -> Type)
        `{E1 -< E}
        `{E2 -< E}
        T (e: E2 T)
    :
      trigger (@inr1 E1 E2 _ e)%sum = (trigger e: itree E T)
  .
  Proof. refl. Qed.


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

    (* Ltac hide_left := *)
    (*   match goal with *)
    (*   | [ |- gpaco5 _ _ _ _ _ _ _ ?i_src ?i_tgt ] => let name := fresh "HIDDEN" in remember i_src as HIDDEN *)
    (*   end. *)
    (* hide_left. *)
    steps.
    destruct (alist_find fn stb) eqn:FINDFT; cycle 1.
    { steps. }
    (* unfold ModSemL.prog at 2. steps. *)
    unfold HoareCall.
    steps. unfold put, guarantee. steps.
    destruct st_tgt0 as [rst_tgt0 pst_tgt0]. destruct st_src0 as [rst_src0 pst_src0].
    (* Opaque interp_Es. (*** TODO: move to ModSemL ***) *)
    destruct (varg_src↓) eqn:CAST; cycle 1.
    { steps. }
    steps. unfold handle_rE. destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]] eqn:T; ss.
    { rr in SIM. des_ifs_safe. des; ss. destruct l; ss. }



    (*** exploiting both_tau ***)
    unseal_left. ired_both. destruct (alist_find fn stb) eqn:STBFIND.
    2:{ steps. }
    ss. steps. rewrite CAST.


    unfold discard. steps.
    unfold guarantee. steps. (*** TODO: remove: unfold guarantee ***)
    (* do 2 (mred; try _step; des_ifs_safe). *)
    (* unseal_left. *)
    (* seal_right. _step. exists (x2↑). mred. unseal_right. *)
    (* _step. instantiate (1:=Ordinal.from_nat 300). *)
    (* assert(idK_spec2: forall E A B (a: A) (itr: itree E B), itr = Ret a >>= fun _ => itr). *)
    (* { i. ired. ss. } *)
    (* match goal with *)
    (* | [ |- gpaco5 _ _ _ _ _ _ _ ?i_src ?i_tgt ] => erewrite idK_spec2 with (itr := i_tgt) *)
    (* end. *)
    (* guclo bindC_spec. *)
    (* replace (Ordinal.from_nat 80) with (Ordinal.add (Ordinal.from_nat 70) (Ordinal.from_nat 10)) by admit "ez". *)
    (* eapply bindR_intro with (RR:=(fun '((rs_src, v_src)) '((rs_tgt, v_tgt)) => wf rs_src rs_tgt /\ (v_src: ord) = v_tgt)). *)
    (* { des_ifs. *)
    (*   - instantiate(1:=(c1, l, pst_src0, ord_top)). steps. esplits; eauto. steps. des; ss. esplits; ss; et. *)
    (*   - steps. *)
    (* } *)
    (* i; subst. *)
    (* destruct vret_tgt as [[[mrs0 frs0] mps0] ord_cur]. *)
    destruct tbr.
    { des; et. Opaque ord_lt. destruct x4; ss; cycle 1. { exfalso. exploit x7; et. } steps. esplits; eauto. steps. unshelve esplits; eauto. steps. unfold unwrapU.
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
      (* { steps. *)
      (*   rewrite WTY in *. ss. clear - FINDFS FINDFT0. *)
      (*   rewrite find_map in *. uo. des_ifs. *)
      (*   apply_all_once find_some. des. *)
      (*   eapply find_none in Heq0; eauto. *)
      (*   unfold compose in *. des_ifs. ss. des_sumbool. ss. *)
      (* } *)
      instantiate (1:=399).
      mred. steps.
      rename i into i_src.
      rename i0 into i_tgt.
      guclo bindC_spec.
      replace (Ord.from_nat 400) with
          (OrdArith.add (Ord.from_nat 200) (Ord.from_nat 200)); cycle 1.
      { admit "ez". }
      rename f into fs.
      econs.
      - instantiate (1:= fun '((((mrs_src, frs_src), mps_src), vret_src): (r_state * p_state * Any_src))
                             '((((mrs_tgt, frs_tgt), mps_tgt), vret_tgt): (r_state * p_state * Any_tgt)) =>
                           exists (rret: Σ) (vret_src': fs.(AR)),
                             (<<ST: (List.length frs_src) = (List.length frs_tgt) /\
                                    frs_src <> [] /\
                                    URA.wf (rsum (mrs_tgt, rret :: frs_tgt))>>) /\
                             (* (<<VAL: vret_src = vret_tgt>>) /\ *)
                             (<<CAST: vret_src↓ = Some vret_src'>>) /\
                             (<<POST: fs.(postcond) x2 vret_src' vret_tgt rret>>) /\
                             (<<PHYS: mps_src = mps_tgt>>)
                    ).
        apply alist_find_some in FINDFT0.
        apply alist_find_some in FINDFS.
        unfold ms_mid, mds_mid, SMod.to_mid in FINDFS. rewrite SMod.transl_fnsems in FINDFS. unfold SMod.load_fnsems in FINDFS. ss.
        eapply in_flat_map in FINDFS; des. eapply in_flat_map in FINDFS0; des. des_ifs. ss. des; ss. clarify. fold sk in FINDFS0.
        unfold ms_tgt, mds_tgt, SMod.to_tgt in FINDFT0. rewrite SMod.transl_fnsems in FINDFT0. unfold SMod.load_fnsems in FINDFT0. ss.
        eapply in_flat_map in FINDFT0; des. eapply in_flat_map in FINDFT1; des. des_ifs. ss. des; ss. clarify. fold sk in FINDFT1.
        assert(x4 = x9).
        { admit "ez - no function name duplication". }
        subst. rename x9 into md0.
        assert(f = f0).
        { admit "ez - no function name duplication". }
        subst.
        assert(fs = f0).
        { clear - FINDFT0 FINDFS0. admit "ez - no function name duplication". }
        subst.
        fold sk. fold sk. set (mn0:=(SModSem.mn (SMod.get_modsem md0 sk))) in *.
        fold Any_tgt in x3.
        unfold fun_to_src, fun_to_tgt, compose. des_ifs. unfold HoareFun.
        rename x3 into PRECOND. rename x0 into rarg.
        steps. exists (rsum_minus mn0 (update mrs_tgt0 mn c, ε ⋅ rarg :: x1 :: frs_tgt_tl)).
        steps. exists a.
        steps. esplits; et. steps. exists rarg.
        steps. unfold forge, checkWf, assume, guarantee.
        steps.
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
        steps. esplits; eauto. steps. unshelve esplits; eauto. steps.
        unfold fun_to_mid.
        assert(CAST0: varg_src = Any.upcast a).
        { erewrite Any.downcast_upcast; et. }
        rewrite Any.upcast_downcast. steps.
        guclo bindC_spec.
        replace (Ord.from_nat 153) with (OrdArith.add (Ord.from_nat 53) (Ord.from_nat 100)); cycle 1.
        { admit "ez - ordinal nat add". }
        econs.
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
          unfold guarantee. steps. r in SIM. des; ss. rewrite Any.upcast_downcast. esplits; ss; eauto.
          { rewrite rsum_minus_spec in x3. rewrite URA.add_assoc in x3.
            rewrite <- rsum_update in x3.
            rewrite rsum_cons. rewrite URA.add_comm.
            rewrite rsum_cons. rewrite <- URA.add_assoc.
            rewrite URA.add_comm. rewrite <- URA.add_assoc. auto.
          }
      - ii. ss. des_ifs_safe. des. (* rr in SIM0. des; ss. unfold RelationPairs.RelCompFun in *. ss. *)
        (* r in SIM0. des_ifs. des; ss. *)
        unfold checkWf, assume; steps. clear_tac. esplits. steps.
        unfold forge; steps. des_ifs; ss. { steps. } steps. exists vret_src'. instantiate (1:=rret). esplits; et.
        steps. exists (rsum_minus mn (c3, c0 ⋅ rret :: l1)).
        steps. unshelve esplits; eauto.
        { rewrite rsum_minus_spec. rewrite URA.add_assoc.
          rewrite <- rsum_update. rewrite update_same.
          rewrite rsum_cons in ST1. rewrite rsum_cons in ST1. rewrite rsum_cons in ST1.
          eapply URA.wf_mon. instantiate (1:=c5).
          replace (rsum (c3, l1) ⋅ (c0 ⋅ rret) ⋅ c5) with (rret ⋅ (c5 ⋅ (c0 ⋅ rsum (c3, l1)))); auto.
          r_solve.
        }
        steps. unshelve esplits; eauto. steps.
        gbase. eapply Any.downcast_upcast in CAST0. des. subst. eapply CIH; ss.
        rr. esplits; et. { destruct l2; ss. } clear - ST1.
        { eapply URA.wf_mon. instantiate (1:=c5).
          rewrite ! rsum_cons. rewrite ! rsum_cons in ST1.
          replace (c0 ⋅ rret ⋅ rsum (c3, l1) ⋅ c5) with (rret ⋅ (c5 ⋅ (c0 ⋅ rsum (c3, l1)))); auto.
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
                           exists (rret: Σ) (vret_src': fs.(AR)),
                             (<<ST: (List.length frs_src) = (List.length frs_tgt) /\
                                    frs_src <> [] /\
                                    URA.wf (rsum (mrs_tgt, rret :: frs_tgt))>>) /\
                             (* (<<VAL: vret_src = vret_tgt>>) /\ *)
                             (<<CAST: vret_src↓ = Some vret_src'>>) /\
                             (<<POST: fs.(postcond) x2 vret_src' vret_tgt rret>>) /\
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
        fold Any_tgt in x3.
        unfold fun_to_src, fun_to_tgt, compose. des_ifs. unfold HoareFun.
        rename x3 into PRECOND. rename x0 into rarg.
        steps. exists (rsum_minus mn0 (update mrs_tgt0 mn c, ε ⋅ rarg :: x1 :: frs_tgt_tl)).
        steps. exists a.
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
        rewrite Any.upcast_downcast.
        steps.
        guclo bindC_spec.
        replace (Ord.from_nat 153) with (OrdArith.add (Ord.from_nat 53) (Ord.from_nat 100)); cycle 1.
        { admit "ez - ordinal nat add". }
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
          unfold handle_rE. destruct r0; ss. destruct l; ss.
          { steps. }
          steps.
          unfold guarantee.
          steps.
          unfold discard.
          steps.
          unfold guarantee. steps. r in SIM. des; ss. rewrite Any.upcast_downcast. esplits; ss; eauto.
          clear - x3 WFTGT0.
          rewrite rsum_minus_spec in x3. rewrite URA.add_assoc in x3.
          rewrite <- rsum_update in x3.
          rewrite rsum_cons. rewrite URA.add_comm.
          rewrite rsum_cons. rewrite <- URA.add_assoc.
          rewrite URA.add_comm. rewrite <- URA.add_assoc. auto.
      - ii. ss. des_ifs_safe. des. (* rr in SIM0. des; ss. unfold RelationPairs.RelCompFun in *. ss. *)
        (* r in SIM0. des_ifs. des; ss. *)
        steps. clear_tac. esplits. steps.
        unfold forge, checkWf, assume; steps.
        des_ifs; ss.
        { steps. }
        steps. esplits. steps. instantiate (1:= rret). instantiate (1:=vret_src').
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
        gbase. eapply Any.downcast_upcast in CAST0. des. subst. eapply CIH; ss.
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
  Variable (mainbody: list val -> itree (hCallE +' pE +' eventE) val).
  Hypothesis MAINPRE: mainpre ([]: list val)↑ ord_top entry_r.

  Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)).

  Hypothesis MAINM: In (SMod.main mainpre mainbody) mds.

  Let MAINF: @alist_find _ _ (@Dec_RelDec string string_Dec) _  "main" stb = Some (mk_simple (fun (_: unit) => (mainpre, top2))).
  Proof.
    unfold stb, _stb.
    rewrite alist_find_map. uo. unfold compose. des_ifs.
    - eapply alist_find_some in Heq. des. des_sumbool. subst. repeat f_equal.
      assert(In ("main", (mk_specbody (mk_simple (fun (_: unit) => (mainpre, top2))) mainbody)) sbtb).
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
                             Beh.of_program (ModL.compile_arg (Mod.add_list mds_mid) (ord_top, []: list val)↑).
  Proof.
    eapply adequacy_global_itree.
    exists (Ord.from_nat 100%nat). ss.
    ginit.
    { eapply cpn6_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr, ModSemL.initial_itr_arg. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.
    unfold assume.
    steps.
    esplits; et.
    { inv x_src. econs.
      { rewrite fns_eq. auto. }
      { pose proof fst_initial_mrs_eq. unfold ms_tgt, ms_mid in H.
        rewrite H. auto. }
    }
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
    eexists. steps. exists []. steps. exists tt. steps.
    eexists. steps. unshelve esplits.
    { admit "resource wf". }
    steps. exists ord_top. steps. unshelve esplits.
    { red. uipropall. split.
      { eapply MAINPRE. }
      { red. uipropall. }
    }
    steps.
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
      steps. uipropall. des. red in x4. uipropall.
    }
    Unshelve.
    all: try (by apply Ord.O).
    all: try (by apply 0%nat).
  Qed.

End CANCEL.
