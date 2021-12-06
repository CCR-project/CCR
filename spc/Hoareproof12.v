Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Import ModSemL.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef.
Require Import SimSTS.
Require Import SimGlobal2.
Require Import HoareDef.
From Ordinal Require Import Ordinal Arithmetic.

Set Implicit Arguments.

































Inductive opair: Type := mk_opair { ofst: Ord.t; osnd: Ord.t }.
(* Definition opair_lt: opair -> opair -> Prop := fun '(mk_opair x0 x1) '(mk_opair y0 y1) => (x0 < y0)%ord \/ (x0 == y0 /\ x1 < y1)%ord. *)
Inductive opair_lt: opair -> opair -> Prop :=
| intro_opair_lt
    x0 x1 y0 y1
    (LT: (x0 < y0)%ord \/ (x0 == y0 /\ x1 < y1)%ord)
  :
    opair_lt (mk_opair x0 x1) (mk_opair y0 y1)
.
Theorem wf_opair_lt: well_founded opair_lt.
Proof.
  ii. destruct a.
  revert osnd0. pattern ofst0. eapply well_founded_ind. { eapply Ord.lt_well_founded. } clear ofst0. intros ? IH0.
  intro. generalize dependent x. pattern osnd0. eapply well_founded_ind. { eapply Ord.lt_well_founded. } clear osnd0. intros ? IH1.
  econs. i. inv H. des.
  { eapply IH0; et. }
  { eapply IH1; et. i. eapply IH0; et. rewrite <- LT. ss. }
Qed.











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
  Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) sk) mds).
  Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss).
  Let _stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb.

  Variable stb: gname -> option fspec.
  Hypothesis STBCOMPLETE:
    forall fn fsp (FIND: alist_find fn _stb = Some fsp), stb fn = Some fsp.
  Hypothesis STBSOUND:
    forall fn (FIND: alist_find fn _stb = None),
      (<<NONE: stb fn = None>>) \/ (exists fsp, <<FIND: stb fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>).


  Let mds_mid2: list Mod.t := List.map (SMod.to_mid2 stb) mds.
  Let mds_mid: list Mod.t := List.map (SMod.to_mid stb) mds.



  Let W: Type := p_state.
  (* Let wf: Ord.t -> W -> W -> Prop := top3. *)

  Opaque EventsL.interp_Es.

  Let ms_mid2: ModSemL.t := ModL.enclose (Mod.add_list mds_mid2).
  Let ms_mid: ModSemL.t := ModL.enclose (Mod.add_list mds_mid).

  Let p_mid2 := ModSemL.prog ms_mid2.
  Let p_mid := ModSemL.prog ms_mid.

  Ltac _step tac :=
    match goal with
    (*** terminal cases ***)
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (triggerUB >>= _) _ ] =>
      unfold triggerUB; mred; _step tac; ss; fail
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (triggerNB >>= _) _ ] =>
      exfalso
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (triggerUB >>= _) ] =>
      exfalso
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (triggerNB >>= _) ] =>
      unfold triggerNB; mred; _step tac; ss; fail

    (*** assume/guarantee ***)
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (assume ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (assume ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar

    (*** default cases ***)
    | _ =>
      (tac; econs; auto;
       (*** some post-processing ***)
       i;
       try match goal with
           | [ |- (eq ==> _)%signature _ _ ] =>
             let v_src := fresh "v_src" in
             let v_tgt := fresh "v_tgt" in
             intros v_src v_tgt ?; subst v_tgt
           end)
    end
  .

  Ltac steps := repeat (mred; try _step ltac:(guclo simg_safe_spec); des_ifs_safe).
  Ltac steps_strong := repeat (mred; try (_step ltac:(guclo simg_indC_spec)); des_ifs_safe).

  Lemma stb_find_iff_aux fn
    :
      ((<<NONE: alist_find fn _stb = None>>) /\
       (<<FINDSRC: alist_find fn (fnsems ms_mid2) = None>>) /\
       (<<FINDMID: alist_find fn (fnsems ms_mid) = None>>)) \/

      (exists md (f: fspecbody),
          (<<SOME: alist_find fn _stb = Some (f: fspec)>>) /\
          (<<FINDSRC: alist_find fn (fnsems ms_mid2) =
                      Some (transl_all (T:=_)
                              (SModSem.mn
                                 (SMod.get_modsem md sk))
                              ∘ fun_to_mid2 (fsb_body f))>>) /\
          (<<FINDMID: alist_find fn (fnsems ms_mid) =
                      Some (transl_all (T:=_)
                              (SModSem.mn
                                 (SMod.get_modsem md sk))
                              ∘ fun_to_mid stb (fsb_body f))>>)).
  Proof.
    unfold ms_mid2, ms_mid, mds_mid, mds_mid2, SMod.to_mid2, SMod.to_mid.
    rewrite SMod.transl_fnsems. rewrite SMod.transl_fnsems. fold sk.
    unfold _stb at 1 2. unfold sbtb, mss. rewrite alist_find_map.
    generalize mds. induction mds0; ss; auto. rewrite ! alist_find_app_o.
    erewrite ! SMod.red_do_ret2. rewrite ! alist_find_map. uo.
    destruct (alist_find fn (SModSem.fnsems (SMod.get_modsem a sk))) eqn:FIND.
    { right. esplits; et. }
    des.
    { left. esplits; et. }
    { right. esplits; et. }
  Qed.

  Lemma stb_find_iff fn
    :
      ((<<NONE: stb fn = None>> \/ (exists fsp, <<FIND: stb fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>)) /\
       (<<FINDSRC: alist_find fn (fnsems ms_mid2) = None>>) /\
       (<<FINDMID: alist_find fn (fnsems ms_mid) = None>>)) \/

      (exists md (f: fspecbody),
          (<<STB: stb fn = Some (f: fspec)>>) /\
          (<<FINDSRC: alist_find fn (fnsems ms_mid2) =
                      Some (transl_all (T:=_)
                              (SModSem.mn
                                 (SMod.get_modsem md sk))
                              ∘ fun_to_mid2 (fsb_body f))>>) /\
          (<<FINDMID: alist_find fn (fnsems ms_mid) =
                      Some (transl_all (T:=_)
                              (SModSem.mn
                                 (SMod.get_modsem md sk))
                              ∘ fun_to_mid stb (fsb_body f))>>)).
  Proof.
    hexploit (stb_find_iff_aux fn). i. des.
    { left. esplits; et. }
    { right. esplits; et. }
  Qed.

  Let adequacy_type_aux__APC:
    forall at_most o0 mn
           st_src0 st_tgt0
    ,
      simg (fun (st_src1: p_state * unit) '(st_tgt1, x) => st_tgt1 = st_tgt0)
           false false (Ret (st_src0, tt))
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid stb (ord_pure o0) (_APC at_most))) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    (* induction *)
    intros ? ?. remember (mk_opair o0 at_most) as fuel. move fuel at top. revert at_most o0 Heqfuel.
    pattern fuel. eapply well_founded_induction. { eapply wf_opair_lt. } clear fuel.
    intros fuel IH. i.

    rewrite unfold_APC. steps.
    destruct x.
    { steps. }
    steps. hexploit (stb_find_iff s). i. des.
    { rewrite NONE. steps. }
    { rewrite FIND. steps. exfalso. eapply x1; et. }
    rewrite STB. steps.
    steps. rewrite FINDMID. unfold fun_to_mid. steps.
   rewrite idK_spec at 1.
    guclo bindC_spec. econs.
    { unfold APC. steps. eapply simg_flag_down.
      eapply IH; auto. econs. left. auto.
    }

    i. ss. destruct vret_tgt as [? []]. destruct vret_src as [? []]. ss. des; subst.
    unfold idK. steps. eapply simg_flag_down.
    eapply IH; et. econs; et. right; split; et. refl.
  Qed.

  Let adequacy_type_aux_APC:
    forall o0 st_src0 st_tgt0 mn
    ,
      simg (fun (st_src1: p_state * unit) '(st_tgt1, _) => st_tgt1 = st_tgt0)
           false false (Ret (st_src0, tt))
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid stb (ord_pure o0) APC)) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    i. unfold APC. steps. eapply simg_flag_down.
    gfinal. right.
    eapply adequacy_type_aux__APC.
    Unshelve. all: try exact 0.
  Qed.

  Lemma idK_spec2: forall E A B (a: A) (itr: itree E B), itr = Ret a >>= fun _ => itr. Proof. { i. ired. ss. } Qed.

  Let adequacy_type_aux:
    forall
      o0
      A (body: itree _ A) st_src0 st_tgt0 mn
      (SIM: st_tgt0 = st_src0)
    ,
      simg eq
           false false
           (EventsL.interp_Es p_mid2 (transl_all mn (interp_hCallE_mid2 body)) st_src0)
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid stb o0 body)) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    gcofix CIH. i. ides body.
    { steps. }
    { steps. eapply simg_progress_flag. gbase. eapply CIH; ss. }

    destruct e; cycle 1.
    { rewrite <- bind_trigger. resub. steps.
      destruct s; ss.
      { destruct p; resub; ss.
        - steps. eapply simg_progress_flag. gbase. eapply CIH; ss; et.
        - steps. eapply simg_progress_flag. gbase. eapply CIH; ss; et.
      }
      { dependent destruction e; resub; ss.
        - steps. steps_strong. exists x. steps. eapply simg_progress_flag. gbase. eapply CIH; et.
        - steps. steps_strong. exists x. steps. eapply simg_progress_flag. gbase. eapply CIH; et.
        - steps_strong. eapply simg_progress_flag. gbase. eapply CIH; et.
      }
    }
    dependent destruction h.
    rewrite <- bind_trigger. resub.
    ired_both. hexploit (stb_find_iff fn). i. des.
    { rewrite NONE. steps. }
    { rewrite FIND. steps. destruct tbr.
      { exfalso. eapply x; ss. }
      steps. rewrite FINDSRC. steps.
    }
    rewrite STB. steps. destruct tbr.
    (* PURE *)
    { Local Opaque ord_lt. ired_both. steps.
      rewrite FINDMID. unfold fun_to_mid. ired_both.
      rewrite idK_spec2 at 1.
      guclo bindC_spec. econs.
      { eapply simg_flag_down. gfinal. right. eapply paco7_mon. { eapply adequacy_type_aux_APC. } ii; ss. }
      i. steps. steps_strong. exists x2. steps. eapply simg_progress_flag.
      gbase. eapply CIH. ss.
    }

    (* IMPURE *)
    { Local Opaque ord_lt. unfold guarantee. steps.
      rewrite FINDMID. rewrite FINDSRC.
      unfold fun_to_mid2, cfunN, fun_to_mid. steps.
      guclo bindC_spec. econs.
      { eapply simg_progress_flag. gbase. eapply CIH. ss. }
      i. subst. steps.
      steps.
      eapply simg_progress_flag. gbase. eapply CIH. ss.
    }
    Unshelve. all: ss.
  Qed.

  Lemma sk_eq:
    ModL.sk (Mod.add_list mds_mid) = ModL.sk (Mod.add_list mds_mid2).
  Proof.
    unfold ms_mid, ms_mid2, mds_mid2, mds_mid, ModL.enclose.
    rewrite ! Mod.add_list_sk. f_equal.
    generalize mds. clear. i. induction mds; ss.
    rewrite IHl. auto.
  Qed.

  Lemma initial_mrs_eq:
    initial_mrs ms_mid = initial_mrs ms_mid2.
  Proof.
    pose proof sk_eq.
    unfold ms_mid, ms_mid2, mds_mid2, mds_mid, ModL.enclose.
    unfold mds_mid2, mds_mid in H. rewrite H.
    generalize (ModL.sk (Mod.add_list (List.map (SMod.to_mid2 stb) mds))). i.
    rewrite ! Mod.add_list_initial_mrs.
    generalize mds. clear. i. induction mds; auto.
    ss. rewrite IHl. auto.
  Qed.

  Lemma fns_eq:
    (List.map fst (fnsems (ModL.enclose (Mod.add_list mds_mid))))
    =
    (List.map fst (fnsems (ModL.enclose (Mod.add_list mds_mid2)))).
  Proof.
    pose proof sk_eq. unfold ModL.enclose.
    unfold mds_mid2, mds_mid, ModL.enclose.
    unfold mds_mid2, mds_mid in H. rewrite H.
    generalize (ModL.sk (Mod.add_list (List.map (SMod.to_mid2 stb) mds))). i.
    rewrite ! Mod.add_list_fns. rewrite ! List.map_map. f_equal.
    f_equal. extensionality sm. ss. rewrite ! List.map_map. f_equal.
    extensionality fnsb. destruct fnsb as [fn sb]. ss.
  Qed.

  Context `{CONF: EMSConfig}.
  Definition midConf: EMSConfig := {| finalize := finalize; initial_arg := Any.pair ord_top↑ initial_arg |}.
  Theorem adequacy_type_m2m:
    Beh.of_program (@ModL.compile _ midConf (Mod.add_list mds_mid)) <1=
    Beh.of_program (ModL.compile (Mod.add_list mds_mid2)).
  Proof.
    eapply adequacy_global_itree; ss.
    ginit.
    { eapply cpn7_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr, ModSemL.initial_itr. Local Opaque ModSemL.prog. ss.
    unfold ITree.map. steps.
    Local Transparent ModSemL.prog.
    unfold ModSemL.prog at 4.
    unfold ModSemL.prog at 2.
    Local Opaque ModSemL.prog.
    ss. steps_strong.
    esplits; et.
    { des. inv x. split.
      { inv H. econs.
        { rewrite fns_eq. auto. }
        { pose proof initial_mrs_eq. unfold ms_mid, ms_mid2 in H.
          rewrite H. auto. }
      }
      { ss. rewrite sk_eq. auto. }
    }
    steps.

    (* stb main *)
    hexploit (stb_find_iff "main"). i. des.
    { unfold ms_mid2 in FINDSRC. rewrite FINDSRC. steps. }
    { unfold ms_mid2 in FINDSRC. rewrite FINDSRC. steps. }

    fold ms_mid2. fold ms_mid.
    rewrite FINDSRC. rewrite FINDMID. steps.
    unfold fun_to_mid2, fun_to_mid, cfunN. steps.
    guclo bindC_spec. econs.
    { eapply simg_flag_down. gfinal. right. eapply adequacy_type_aux. ss.
      unfold initial_p_state.
      rewrite initial_mrs_eq. auto. }
    { i. subst. steps. }
  Qed.

End CANCEL.
