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

Generalizable Variables E R A B C X Y Σ.

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

  Let mds_mid: list Mod.t := List.map (SMod.to_mid) mds.
  Let mds_tgt: list Mod.t := List.map (SMod.to_tgt _stb) mds.

  Let ms_mid: ModSemL.t := ModL.enclose (Mod.add_list mds_mid).
  Let ms_tgt: ModSemL.t := ModL.enclose (Mod.add_list mds_tgt).

  Let W: Type := (r_state * p_state).
  Let rsum: r_state -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (fold_left (⋅) (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) ⋅ (fold_left (⋅) frs_tgt ε).

  Let wf: W -> W -> Prop :=
    fun '((mrs_src, frs_src), mps_src) '((mrs_tgt, frs_tgt), mps_tgt) =>
      (<<LEN: List.length frs_src = List.length frs_tgt>>) /\
      (<<NNIL: frs_src <> []>>) /\
      (<<WFTGT: URA.wf (rsum (mrs_tgt, frs_tgt))>>) /\
      (<<PHYS: mps_src = mps_tgt>>)
  .
  Local Opaque rsum.

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

  Ltac resub :=
    repeat multimatch goal with
           | |- context[ITree.trigger ?e] =>
             match e with
             | subevent _ _ => idtac
             | _ => replace (ITree.trigger e) with (trigger e) by refl
             end
           | |- context[@subevent _ ?F ?prf _ (?e|)%sum] => replace (@subevent _ F prf _ (e|)%sum) with (@subevent _ F _ _ e) by refl
           | |- context[@subevent _ ?F ?prf _ (|?e)%sum] => replace (@subevent _ F prf _ (|e)%sum) with (@subevent _ F _ _ e) by refl
           end.

  Let adequacy_type_aux:
    forall RT
           st_src0 st_tgt0 (SIM: wf st_src0 st_tgt0) (i0: itree (hCallE +' pE +' eventE) RT)
           mn cur
    ,
      (* sim (Mod.compile md_src) (Mod.compile md_tgt) lt 100%nat *)
      (*     (x <- (interp_Es p_src (interp_hCallE_src (trigger ce)) st_src0);; Ret (snd x)) *)
      (*     (x <- (interp_Es p_tgt (interp_hCallE_tgt stb (trigger ce)) st_tgt0);; Ret (snd x)) *)
      simg (fun '((rs_src, v_src)) '((rs_tgt, v_tgt)) => wf rs_src rs_tgt /\ (v_src: RT) = v_tgt)
           (Ord.from_nat 100%nat)
           (EventsL.interp_Es (ModSemL.prog ms_mid) (transl_all mn (interp_hCallE_mid (E:=pE +' eventE) cur i0)) st_src0)
           (EventsL.interp_Es (ModSemL.prog ms_tgt) (transl_all mn (interp_hCallE_tgt (E:=pE +' eventE) stb cur i0)) st_tgt0)
           (* (interp_Es mn (ModSemL.prog ms_mid) ((interp_hCallE_mid (E:=pE +' eventE) cur i0)) st_src0) *)
           (* (interp_Es mn (ModSemL.prog ms_tgt) ((interp_hCallE_tgt (E:=pE +' eventE) stb cur i0)) st_tgt0) *)
  .
  Proof.
    Opaque subevent.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
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
        - rewrite <- bind_trigger. resub. steps. gbase. eapply CIH. ss.
        - rewrite <- bind_trigger. resub. steps. gbase. eapply CIH. ss.
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
    unseal_left. ired_both. steps.




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
      destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_mid)) eqn:FINDFS; cycle 1.
      { steps. }
      destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_tgt)) eqn:FINDFT0; cycle 1.
      { steps.
        apply find_some in FINDFS. des. des_sumbool. subst. destruct p as [fn fsem]; ss.
        assert(IN: In fn (List.map fst ms_mid.(ModSemL.fnsems))).
        { rewrite in_map_iff. esplits; et. ss. }
        unfold ms_mid in IN. unfold mds_mid in IN. unfold SMod.to_mid in IN.
        erewrite SMod.transl_fnsems_stable with (tr1:=(fun_to_tgt ∘ _stb)) (mr1:=SModSem.initial_mr) in IN.
        replace (SMod.transl (fun_to_tgt ∘ _stb) SModSem.initial_mr) with (SMod.to_tgt _stb) in IN by refl.
        fold mds_tgt in IN. fold ms_tgt in IN.
        rewrite in_map_iff in IN. des. subst.
        eapply find_none in FINDFT0; et.
        des_sumbool. ss.
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
        apply find_some in FINDFT0. des.
        apply find_some in FINDFS. des. ss. des_sumbool. clarify.
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
        { clear - FINDFT FINDFS0. admit "ez - no function name duplication". }
        subst.
        fold sk. fold sk. set (mn0:=(SModSem.mn (SMod.get_modsem md0 sk))) in *.
        fold Any_tgt in x3.
        unfold fun_to_src, fun_to_tgt, compose. des_ifs. unfold HoareFun.
        rename x3 into PRECOND. rename x0 into rarg.
        steps. exists a.
        steps. esplits; et. steps. exists rarg.
        steps. unfold forge, checkWf. steps. unfold assume, guarantee.
        steps. unshelve esplits; eauto.
        { clear - WFTGT x. rewrite URA.unit_idl. rewrite URA.add_assoc in x.
          r in x. specialize (x URA.unit). rewrite ! URA.unit_id in x.
          unfold update. des_ifs.
          - eapply URA.wf_mon. eapply x. admit "ez - WFTGT".
          - admit "ez - c1 contains both (c1 mn0) and (c1 (mn fs)).".
        }
        steps. esplits; eauto. steps. unfold cfun. steps. unshelve esplits; eauto. steps.
        unfold fun_to_mid.
        assert(CAST0: varg_src = Any.upcast a).
        { erewrite Any.downcast_upcast; et. }
        rewrite CAST0.
        assert(Any_pair_downcast: forall T0 T1 (v0: T0) (v1: T1), @Any.downcast (T0 * T1)%type (Any.pair v0↑ v1↑) = Some (v0, v1)).
        { admit "ez - add this to Any.v ------------------". }
        rewrite Any_pair_downcast.
        steps.
        guclo bindC_spec.
        replace (Ord.from_nat 158) with (OrdArith.add (Ord.from_nat 58) (Ord.from_nat 100)); cycle 1.
        { admit "ez - ordinal nat add". }
        econs.
        + gbase. eapply CIH. rr. esplits; ss; et. rewrite URA.unit_idl. clear - WFTGT x. admit "ez".
        + ii. ss. des_ifs_safe. des; ss. clarify. des_u.
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
          admit "ez".
      - ii. ss. des_ifs_safe. des. (* rr in SIM0. des; ss. unfold RelationPairs.RelCompFun in *. ss. *)
        (* r in SIM0. des_ifs. des; ss. *)
        unfold checkWf, assume; steps. clear_tac. esplits. steps.
        unfold forge; steps. des_ifs; ss. { steps. } steps. exists vret_src'. instantiate (1:=rret). esplits; et.
        steps. unshelve esplits; eauto. { clear - ST1. admit "ez". } steps. unshelve esplits; eauto. steps.
        gbase. eapply Any.downcast_upcast in CAST0. des. subst. eapply CIH.
        rr. esplits; et. { destruct l2; ss. } clear - ST1. admit "ez".
    }
    { des. clear x7. exploit x8; et. i; clarify. clear x8.
      steps. esplits; eauto. steps. esplits; eauto. steps. unfold unwrapU.
      destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_mid)) eqn:FINDFS; cycle 1.
      { steps. }
      destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_tgt)) eqn:FINDFT0; cycle 1.
      { steps.
        apply find_some in FINDFS. des. des_sumbool. subst. destruct p as [fn fsem]; ss.
        assert(IN: In fn (List.map fst ms_mid.(ModSemL.fnsems))).
        { rewrite in_map_iff. esplits; et. ss. }
        unfold ms_mid in IN. unfold mds_mid in IN. unfold SMod.to_mid in IN.
        erewrite SMod.transl_fnsems_stable with (tr1:=(fun_to_tgt ∘ _stb)) (mr1:=SModSem.initial_mr) in IN.
        replace (SMod.transl (fun_to_tgt ∘ _stb) SModSem.initial_mr) with (SMod.to_tgt _stb) in IN by refl.
        fold mds_tgt in IN. fold ms_tgt in IN.
        rewrite in_map_iff in IN. des. subst.
        eapply find_none in FINDFT0; et.
        des_sumbool. ss.
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
        apply find_some in FINDFT0. des.
        apply find_some in FINDFS. des. ss. des_sumbool. clarify.
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
        { clear - FINDFT FINDFS0. admit "ez - no function name duplication". }
        subst.
        fold sk. fold sk. set (mn0:=(SModSem.mn (SMod.get_modsem md0 sk))) in *.
        fold Any_tgt in x3.
        unfold fun_to_src, fun_to_tgt, compose. des_ifs. unfold HoareFun.
        rename x3 into PRECOND. rename x0 into rarg.
        steps. exists a.
        steps. esplits; et. steps. exists rarg.
        steps. unfold forge, checkWf. steps. unfold assume, guarantee.
        steps. unshelve esplits; eauto.
        { clear - WFTGT x. rewrite URA.unit_idl. rewrite URA.add_assoc in x.
          r in x. specialize (x URA.unit). rewrite ! URA.unit_id in x.
          unfold update. des_ifs.
          - eapply URA.wf_mon. eapply x. admit "ez - WFTGT".
          - admit "ez - c1 contains both (c1 mn0) and (c1 (mn fs)).".
        }
        steps. esplits; eauto. steps. unfold cfun. steps. unshelve esplits; eauto. steps.
        unfold fun_to_mid.
        assert(CAST0: varg_src = Any.upcast a).
        { erewrite Any.downcast_upcast; et. }
        rewrite CAST0.
        assert(Any_pair_downcast: forall T0 T1 (v0: T0) (v1: T1), @Any.downcast (T0 * T1)%type (Any.pair v0↑ v1↑) = Some (v0, v1)).
        { admit "ez - add this to Any.v ------------------". }
        rewrite Any_pair_downcast.
        steps.
        guclo bindC_spec.
        replace (Ord.from_nat 158) with (OrdArith.add (Ord.from_nat 58) (Ord.from_nat 100)); cycle 1.
        { admit "ez - ordinal nat add". }
        econs.
        + gbase. unfold body_to_tgt, body_to_mid. eapply CIH.
          rr. esplits; ss; et. rewrite URA.unit_idl. clear - WFTGT x. admit "ez".
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
          admit "ez".
      - ii. ss. des_ifs_safe. des. (* rr in SIM0. des; ss. unfold RelationPairs.RelCompFun in *. ss. *)
        (* r in SIM0. des_ifs. des; ss. *)
        steps. clear_tac. esplits. steps.
        unfold forge, checkWf, assume; steps.
        des_ifs; ss.
        { steps. }
        steps. esplits. steps. instantiate (1:= rret). instantiate (1:=vret_src').
        unshelve esplits; eauto.
        { clear - ST1. admit "ez". }
        steps. unshelve esplits; eauto.
        steps.
        gbase. eapply Any.downcast_upcast in CAST0. des. subst. eapply CIH.
        rr. esplits; et. { destruct l2; ss. } clear - ST1. admit "ez".
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
    (fun mn => match List.find (fun mnr => dec mn (fst mnr)) ms.(ModSemL.initial_mrs) with
               | Some r => fst (snd r)
               | None => ε
               end, [entry_r]). (*** we have a dummy-stack here ***)

  Opaque EventsL.interp_Es.

  Theorem adequacy_type_t2m: Beh.of_program (ModL.compile (Mod.add_list mds_tgt)) <1=
                             Beh.of_program (ModL.compile (Mod.add_list mds_mid)).
  Proof.
    eapply adequacy_global.
    exists (Ord.from_nat 100%nat). ss.
    ginit.
    { eapply cpn5_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.
    unfold assume.
    steps.
    esplits; et. { admit "ez - wf". } steps.
    folder.
    set (st_mid0 := ((ModSemL.initial_r_state ms_mid), (ModSemL.initial_p_state ms_mid))).
    set (st_midr0 := ((initial_r_state ms_mid ε), (ModSemL.initial_p_state ms_mid))).
    set (st_tgtl0 := ((initial_r_state ms_tgt entry_r), (ModSemL.initial_p_state ms_tgt))).
    set (st_tgt0 := (ModSemL.initial_r_state ms_tgt, (ModSemL.initial_p_state ms_tgt))).
    (* Local Opaque URA.add. *)
    assert(SIM: wf st_midr0 st_tgtl0).
    { r. ss. esplits; ss; et. { admit "ez". } unfold ms_mid. unfold ModSemL.initial_p_state. ss.
      apply func_ext. clear. i.
      unfold ms_tgt, mds_tgt, SMod.to_tgt, mds_mid, SMod.to_mid. rewrite ! SMod.transl_initial_mrs. folder.
      des_ifs; ss; apply_all_once find_some; des; ss; des_sumbool; clarify;
        unfold SMod.load_initial_mrs in *; apply_all_once in_flat_map; des; ss; des; ss; clarify; ss.
      - assert(x = x0).
        { admit "uniqueness of mn". }
        subst; ss.
      - eapply find_none in Heq0; cycle 1.
        { rewrite in_flat_map. esplits; et. ss; et. }
        ss. des_sumbool; ss.
      - eapply find_none in Heq; cycle 1.
        { rewrite in_flat_map. esplits; et. ss; et. }
        ss. des_sumbool; ss.
    }
    unfold mrec.
    (* { *)
    (*   unfold ModSemL.prog at 4. *)
    (*   unfold ModSemL.prog at 2. *)
    (*   unfold unwrapU at 1. des_ifs; cycle 1. { steps. } steps. *)
    (*   rename Heq into MAINSRC. rename i into i_src. *)
    (*   assert(T: exists i_ftb i_tgt, *)
    (*             (<<MAINTGT:find (fun fnsem => dec "main" (fst fnsem)) (ModSemL.fnsems ms_tgt) = *)
    (*                        Some ("main", i_tgt)>>) *)
    (*             /\ (<<FTB: In ("main", i_ftb) ftb>>) *)
    (*             /\ (<<SIM: i_tgt = fun_to_tgt stb "main" i_ftb>>) *)
    (*             /\ (<<SIM: i_src = fun_to_src i_ftb>>) *)
    (*         ). *)
    (*   { apply find_some in MAINSRC. des; ss. des_sumbool. clarify. *)
    (*     apply in_map_iff in MAINSRC. des. des_ifs. *)
    (*     destruct (find (fun fnsem => dec "main" (fst fnsem)) (ModSemL.fnsems ms_tgt)) eqn:T; *)
    (*       rewrite WTY in *; ss; cycle 1. *)
    (*     - eapply find_none in T; ss; et. *)
    (*       { des_sumbool. instantiate (1:= (_, _)) in T. ss. } *)
    (*       rewrite in_map_iff. eexists (_, _). esplits; et. *)
    (*     - apply find_some in T. des; ss. des_sumbool. destruct p; ss. clarify. *)
    (*       rewrite in_map_iff in T. des; ss. des_ifs. *)
    (*       esplits; et. assert(i = i1) by admit "ez - add nodup". clarify. *)
    (*   } *)
    (*   des. clarify. *)
    (*   unfold unwrapU. des_ifs; cycle 1. steps. *)
    (*   unfold fun_to_tgt. des_ifs. ss. unfold fun_to_src. unfold HoareFun. *)
    (*   steps. esplits; et. steps. esplits; et. steps. *)
    (* } *)
    match goal with | [ |- gpaco5 _ _ _ _ _ _ _ _ ?x ] => remember x as tmp end.
    replace (([]: list val)↑) with (Any.pair ord_top↑ ([]: list val)↑) by admit "
      TODO: parameterize semantics with initial value of main; also, use this same initial value in Hoareproof1".
    subst.
    assert(TRANSL: simg eq (Ord.from_nat 100)
(x0 <- EventsL.interp_Es (ModSemL.prog ms_mid)
                 ((ModSemL.prog ms_mid) _ (Call "main" (Any.pair ord_top↑ ([]: list val)↑))) st_mid0;; Ret (snd x0))
(x0 <- EventsL.interp_Es (ModSemL.prog ms_mid)
                 (transl_all "Main" (interp_hCallE_mid (E:=pE +' eventE) ord_top (trigger (hCall false "main" ([]: list val)↑)))) st_midr0;; Ret (snd x0))).
    { clear SIM. ginit. { eapply cpn5_wcompat; eauto with paco. }
      steps.
      replace (Ord.from_nat 91) with (OrdArith.add (Ord.from_nat 50) (Ord.from_nat 41))
        by admit "ez".
      guclo bindC_spec.
      eapply bindR_intro.
      - eapply simg_gpaco_refl. typeclasses eauto.
      - ii. subst. steps. destruct p as [[mrs0 frs0] mps0]; ss. steps. des_ifs. { steps. } steps.
    }
    assert(TRANSR: simg eq (Ord.from_nat 200)
(x0 <- EventsL.interp_Es (ModSemL.prog ms_tgt)
                 (transl_all "Main" (interp_hCallE_tgt (E:=pE +' eventE) stb ord_top (trigger (hCall false "main" ([]: list val)↑)))) st_tgtl0;; Ret (snd x0))
(x0 <- EventsL.interp_Es (ModSemL.prog ms_tgt)
                 ((ModSemL.prog ms_tgt) _ (Call "main" ([]: list val)↑)) st_tgt0;; Ret (snd x0))).
    { clear SIM. ginit. { eapply cpn5_wcompat; eauto with paco. }
      steps. rewrite MAINF. steps. rewrite Any.upcast_downcast. steps.
      unfold HoareCall.
      destruct (find (fun mnr  => dec "Main" (fst mnr)) (ModSemL.initial_mrs ms_tgt)) eqn:MAINR; cycle 1.
      { exfalso. clear - MAINM MAINR.
        unfold ms_tgt, mds_tgt, SMod.to_tgt in MAINR. rewrite SMod.transl_initial_mrs in MAINR. folder.
        unfold SMod.load_initial_mrs in MAINR.
        rewrite SMod.red_do_ret in MAINR. rewrite find_map in MAINR. uo. unfold compose in *. des_ifs. ss.
        eapply find_none in Heq; et. des_sumbool. ss.
      }
      destruct p; ss.
      assert(s = "Main") by admit "ez". clarify.
      steps. eexists ((fst (fst st_tgt0)) "Main", entry_r). steps.
      unfold put, guarantee. repeat (mred; try _step). unshelve esplits; eauto. { unfold Any_src, Any_mid, Any_tgt. (*** COQ BUG !!!!!!!!!!!!!!! ***) rewrite Heq. refl. }
      steps. esplits; et. steps. unfold discard, guarantee. steps. esplits; et. steps. unshelve esplits; et.
      { rewrite URA.unit_id. ss. }
      steps. unfold guarantee. steps. esplits; ss; et. steps. exists (([]: list val)↑).
      steps. esplits; et. steps. esplits; et. steps. unshelve esplits; eauto. { esplits; eauto; ss. } steps.
      replace (update
                 (fun mn0 : string =>
                    match find (fun mnr => dec mn0 (fst mnr)) (ModSemL.initial_mrs ms_tgt) with
                    | Some r => fst (snd r)
                    | None => ε
                    end) "Main" (fst p), [ε; ε], ModSemL.initial_p_state ms_tgt) with st_tgt0; cycle 1.
      { unfold st_tgt0.
        unfold ModSemL.initial_r_state. f_equal. f_equal. apply func_ext. i. unfold update. des_ifs; ss; clarify. }
      replace (Ord.from_nat 129) with (OrdArith.add (Ord.from_nat 50) (Ord.from_nat 79)) by admit "ez".
      guclo bindC_spec.
      eapply bindR_intro with (RR:=eq).
      - fold st_tgt0. eapply simg_gpaco_refl. typeclasses eauto.
      - ii. des_ifs. ss. steps. destruct p0 as [[mrs0 frs0] mps0]. steps. des_ifs.
        { admit "we should use stronger RR, not eq;
we should know that stackframe is not popped (unary property)". }
        steps.
        unfold forge, checkWf, assume. steps. des_ifs.
        { admit "we should use stronger RR, not eq;
we should know that stackframe is not popped (unary property)". }
        steps. rr in x2; des; ss.
    }



    fold ms_mid. fold st_mid0.
    replace (x <- EventsL.interp_Es (ModSemL.prog ms_mid) (ModSemL.prog ms_mid (Call "main" (Any.pair (Any.upcast ord_top) (Any.upcast [])))) st_mid0;; Ret (snd x))
      with
        (x0 <- EventsL.interp_Es (ModSemL.prog ms_mid) (transl_all "Main" (interp_hCallE_mid (E:=pE +' eventE)
                                                                                             ord_top (trigger (hCall false "main" ([]: list val)↑)))) st_midr0;;
         Ret (snd x0)); cycle 1.
    { admit "hard -- by transitivity". }
    replace (x <- EventsL.interp_Es (ModSemL.prog ms_tgt) (ModSemL.prog ms_tgt (Call "main" (Any.upcast []))) st_tgt0;; Ret (snd x))
      with
        (x0 <- EventsL.interp_Es (ModSemL.prog ms_tgt) (transl_all "Main" (interp_hCallE_tgt (E:=pE +' eventE)
                                                                                             stb ord_top (trigger (hCall false "main" ([]: list val)↑))))
                         st_tgtl0;; Ret (snd x0)); cycle 1.
    { admit "hard -- by transitivity". }
    guclo bindC_spec.
    eapply bindR_intro.
    - gfinal. right. fold simg. eapply adequacy_type_aux; ss.
    - ii. ss. des_ifs. des; ss. clarify. steps.
  Unshelve.
    revert WFR. i. (*** dummy action that keeps "WFR" as a requirement; TODO: remove it later ! ! ***)
    all: ss.
    all: try (by apply Ord.O).
  Qed.

End CANCEL.
