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
Require Import Red.

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

  Variable md_tgt: ModL.t.
  Let ms_tgt: ModSemL.t := (ModL.get_modsem md_tgt (Sk.load_skenv md_tgt.(ModL.sk))).

  Variable sbtb: list (gname * fspecbody).
  Let stb: list (gname * fspec) := List.map (fun '(gn, fsb) => (gn, fsb_fspec fsb)) sbtb.
  Hypothesis WTY: ms_tgt.(ModSemL.fnsems) = List.map (fun '(fn, sb) => (fn, fun_to_tgt stb fn sb)) sbtb.
  Let md_mid: ModL.t := md_mid md_tgt sbtb.
  Let ms_mid: ModSemL.t := ms_mid md_tgt sbtb.

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
  Proof. unfold stb. rewrite List.map_map. apply List.map_ext. i. des_ifs. Qed.
  Hypothesis WF1: Forall (fun '(_, sp) => In sp.(mn) (List.map fst ms_tgt.(ModSemL.initial_mrs))) stb.


  (* Ltac grind := repeat (f_equiv; try apply func_ext; ii; try (des_ifs; check_safe)). *)

  (* Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau; *)
  (*                     try rewrite interp_vis; *)
  (*                     try rewrite interp_ret; *)
  (*                     try rewrite interp_tau *)
  (*                     (* try rewrite interp_trigger *) *)
  (*                    ). *)

  Lemma transl_all_unwrapU
        mn R (r: option R)
    :
      transl_all mn (unwrapU r) = unwrapU r
  .
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite transl_all_ret. grind.
    - rewrite transl_all_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma transl_all_unwrapN
        mn R (r: option R)
    :
      transl_all mn (unwrapN r) = unwrapN r
  .
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite transl_all_ret. grind.
    - rewrite transl_all_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma transl_all_assume
        mn (P: Prop)
    :
      transl_all mn (assume P) = assume P;; tau;; Ret (tt)
  .
  Proof.
    unfold assume.
    repeat (try rewrite transl_all_bind; try rewrite bind_bind). grind.
    rewrite transl_all_eventE.
    repeat (try rewrite transl_all_bind; try rewrite bind_bind). grind.
    rewrite transl_all_ret.
    refl.
  Qed.

  Lemma transl_all_guarantee
        mn (P: Prop)
    :
      transl_all mn (guarantee P) = guarantee P;; tau;; Ret (tt)
  .
  Proof.
    unfold guarantee.
    repeat (try rewrite transl_all_bind; try rewrite bind_bind). grind.
    rewrite transl_all_eventE.
    repeat (try rewrite transl_all_bind; try rewrite bind_bind). grind.
    rewrite transl_all_ret.
    refl.
  Qed.



  Ltac _red_transl_all_aux f itr :=
    match itr with
    | ITree.bind' _ _ =>
      instantiate (f:=_continue); eapply transl_all_bind; fail
    | Tau _ =>
      instantiate (f:=_break); apply transl_all_tau; fail
    | Ret _ =>
      instantiate (f:=_continue); apply transl_all_ret; fail
    | trigger ?e =>
      idtac "E";
      instantiate (f:=_break);
      match (type of e) with
      | context[callE] => apply transl_all_callE
      | context[eventE] => apply transl_all_eventE
      | context[pE] => apply transl_all_pE
      | context[rE] => apply transl_all_rE
      | _ => fail 2
      end
    | triggerUB =>
      instantiate (f:=_break); apply transl_all_triggerUB; fail
    | triggerNB =>
      instantiate (f:=_break); apply transl_all_triggerNB; fail
    | unwrapU _ =>
      instantiate (f:=_break); apply transl_all_unwrapU; fail
    | unwrapN _ =>
      instantiate (f:=_break); apply transl_all_unwrapN; fail
    | assume _ =>
      instantiate (f:=_break); apply transl_all_assume; fail
    | guarantee _ =>
      instantiate (f:=_break); apply transl_all_guarantee; fail
    | _ =>
      fail
    end
  .

  Lemma interp_Es_eta
        prog R (itr0 itr1: itree _ R) st0
    :
      itr0 = itr1 -> EventsL.interp_Es prog itr0 st0 = EventsL.interp_Es prog itr1 st0
  .
  Proof. i; subst; refl. Qed.

  Ltac _red_transl_all f :=
    match goal with
    (* | [ |- EventsL.interp_Es _ (ITree.bind' _ (transl_all _ ?itr)) _ = _ ] => *)
    (*   idtac "A"; *)
    (*   eapply interp_Es_eta; eapply bind_eta; _red_transl_all_aux f itr *)
    | [ |- ITree.bind' _ (EventsL.interp_Es _ (transl_all _ ?itr) _) = _ ] =>
      idtac "A";
      eapply bind_eta; eapply interp_Es_eta; _red_transl_all_aux f itr
    | [ |- EventsL.interp_Es _ (transl_all _ ?itr) _ = _] =>
      idtac "B";
      eapply interp_Es_eta; _red_transl_all_aux f itr
    | _ => fail
    end.

  Ltac _red_lsim f :=
    (_red_Es f) || (_red_transl_all f) || (_red_itree f) || (fail).

  Ltac ired_l := try (prw _red_lsim 2 0).
  Ltac ired_r := try (prw _red_lsim 1 0).

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
    unfold interp_hCallE_mid.
    unfold interp_hCallE_tgt.
    ides i0; try rewrite ! unfold_interp; cbn; mred.
    { steps. }
    { steps. gbase. eapply CIH; [..|M]; Mskip et. ss. }
    destruct e; cycle 1.
    {
      destruct s; ss.
      {
        destruct st_src0 as [rst_src0 pst_src0], st_tgt0 as [rst_tgt0 pst_tgt0]; ss. des_ifs. des; clarify.
        destruct p; ss.
        - steps. rewrite embed_l_gen. steps. gbase. eapply CIH. ss.
        - steps. rewrite embed_l_gen. steps. gbase. eapply CIH. ss.
      }
      { dependent destruction e.
        - steps. rewrite embed_r_gen. steps. esplits; eauto. steps.
          gbase. eapply CIH; [..|M]; Mskip et. ss.
        - steps. rewrite embed_r_gen. steps. esplits; eauto. steps.
          gbase. eapply CIH; [..|M]; Mskip et. ss.
        - steps. rewrite embed_r_gen. steps. esplits; eauto. steps.
          gbase. eapply CIH; [..|M]; Mskip et. ss.
      }
    }
    dependent destruction h.
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
    destruct (find (fun '(_fn, _) => dec fn _fn) stb) eqn:FINDFT; cycle 1.
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
      destruct (find (fun fnsem => dec fn (fst fnsem)) (List.map (fun '(fn0, sb) => (fn0, fun_to_mid (HoareDef.mn sb.(fsb_fspec)) sb.(fsb_body))) sbtb)) eqn:FINDFS; cycle 1.
      { steps. }
      destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_tgt)) eqn:FINDFT0; cycle 1.
      { steps.
        rewrite WTY in *. ss. clear - FINDFS FINDFT0.
        rewrite find_map in *. uo. des_ifs.
        apply_all_once find_some. des.
        eapply find_none in Heq0; eauto.
        unfold compose in *. des_ifs. ss. des_sumbool. ss.
      }
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
        rewrite WTY in *. fold Any_src in FINDFS. fold Any_tgt in FINDFT0. rewrite in_map_iff in *. des. des_ifs.
        assert(f0 = f) by admit "ez - uniqueness of idx. Add this as an hypothesis". subst.
        assert(fs = f). {
          rename f into fss.
          apply find_some in FINDFT. des. des_sumbool. clarify.
          unfold stb in FINDFT. rewrite in_map_iff in *. des. des_ifs.
          admit "ez - uniqueness of idx. Add this as an hypothesis".
        } subst.
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
        fold (interp_hCallE_mid). fold (interp_hCallE_tgt stb).
        gbase. eapply Any.downcast_upcast in CAST0. des. subst. eapply CIH.
        rr. esplits; et. { destruct l2; ss. } clear - ST1. admit "ez".
    }
    { des. clear x7. exploit x8; et. i; clarify. clear x8.
      steps. esplits; eauto. steps. esplits; eauto. steps. unfold unwrapU.
      destruct (find (fun fnsem => dec fn (fst fnsem)) (List.map (fun '(fn0, sb) => (fn0, fun_to_mid sb.(fsb_fspec).(HoareDef.mn) sb.(fsb_body))) sbtb)) eqn:FINDFS; cycle 1.
      { steps. }
      destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_tgt)) eqn:FINDFT0; cycle 1.
      { exfalso.
        rewrite WTY in *. ss. clear - FINDFS FINDFT0.
        rewrite find_map in *. uo. des_ifs.
        apply_all_once find_some. des.
        eapply find_none in Heq0; eauto.
        unfold compose in *. des_ifs. ss. des_sumbool. ss.
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
        rewrite WTY in *. fold Any_src in FINDFS. fold Any_tgt in FINDFT0. rewrite in_map_iff in *. des. des_ifs.
        assert(f0 = f) by admit "ez - uniqueness of idx. Add this as an hypothesis". subst.
        assert(fs = f). {
          rename f into fss.
          apply find_some in FINDFT. des. des_sumbool. clarify.
          unfold stb in FINDFT. rewrite in_map_iff in *. des. des_ifs.
          admit "ez - uniqueness of idx. Add this as an hypothesis".
        } subst.
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
        fold interp_hCallE_src. fold (interp_hCallE_tgt stb).
        gbase. eapply Any.downcast_upcast in CAST0. des. subst. eapply CIH.
        rr. esplits; et. { destruct l2; ss. } clear - ST1. admit "ez".
    }
  Unshelve.
    all: ss.
    all: try (by apply Ord.O).
    { apply 0. }
  Qed.

  Variable entry_r: Σ.
  Variable main_pre: unit -> Any.t -> ord -> Σ -> Prop.
  Hypothesis MAINPRE: main_pre tt ([]: list val)↑ ord_top entry_r.
  Hypothesis MAIN: List.find (fun '(_fn, _) => dec "main" _fn) stb = Some ("main", (@mk_simple _ "Main" unit main_pre top3)).
  Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)).

  Let initial_r_state ms entry_r: r_state :=
    (fun mn => match List.find (fun mnr => dec mn (fst mnr)) ms.(ModSemL.initial_mrs) with
               | Some r => fst (snd r)
               | None => ε
               end, [entry_r]). (*** we have a dummy-stack here ***)

  Opaque EventsL.interp_Es.

  Theorem adequacy_type_t2m: Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_mid).
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
      apply func_ext. clear. i. rewrite ! find_map; ss. unfold compose. uo. unfold ms_tgt.
      des_ifs; ss; apply_all_once find_some; des; ss; des_sumbool; clarify.
      - destruct p0; ss. admit "ez - uniqueness of s".
      - eapply find_none in Heq0; et. ss. des_sumbool; ss.
      - eapply find_none in Heq1; et. des_ifs. ss. des_sumbool; ss.
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
      unfold interp_hCallE_mid. rewrite unfold_interp. ss.
      Local Transparent subevent. cbn. Local Opaque subevent. steps.
      unfold guarantee. steps.
      replace (Ord.from_nat 91) with (OrdArith.add (Ord.from_nat 50) (Ord.from_nat 41))
        by admit "ez".
      guclo bindC_spec.
      eapply bindR_intro.
      - eapply simg_gpaco_refl. typeclasses eauto.
      - ii. subst. steps. destruct p as [[mrs0 frs0] mps0]; ss. steps. des_ifs. { steps. } steps. interp_red. steps.
    }
    assert(TRANSR: simg eq (Ord.from_nat 200)
(x0 <- EventsL.interp_Es (ModSemL.prog ms_tgt)
                 (transl_all "Main" (interp_hCallE_tgt (E:=pE +' eventE) stb ord_top (trigger (hCall false "main" ([]: list val)↑)))) st_tgtl0;; Ret (snd x0))
(x0 <- EventsL.interp_Es (ModSemL.prog ms_tgt)
                 ((ModSemL.prog ms_tgt) _ (Call "main" ([]: list val)↑)) st_tgt0;; Ret (snd x0))).
    { clear SIM. ginit. { eapply cpn5_wcompat; eauto with paco. }
      unfold interp_hCallE_tgt. rewrite unfold_interp. steps.
      Local Transparent subevent. cbn. Local Opaque subevent.
      steps. rewrite MAIN. steps. rewrite Any.upcast_downcast. steps.
      unfold HoareCall.
      destruct (find (fun mnr  => dec "Main" (fst mnr)) (ModSemL.initial_mrs ms_tgt)) eqn:MAINR; cycle 1.
      { exfalso. clear - WF1 MAIN MAINR. admit "ez - use WF1". }
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
        steps. interp_red. des; ss. steps.
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
