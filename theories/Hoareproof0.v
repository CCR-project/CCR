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
Require Import Logic.
Require Import List.
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

  Variable stb: Sk.t -> gname -> option fspec.
  Hypothesis STBCOMPLETE:
    forall fn fsp (FIND: alist_find fn (_stb sk) = Some fsp), stb sk fn = Some fsp.
  Hypothesis STBSOUND:
    forall fn (FIND: alist_find fn (_stb sk) = None),
      (<<NONE: stb sk fn = None>>) \/ (exists fsp, <<FIND: stb sk fn = Some fsp>> /\ <<TRIVIAL: forall mn x arg_src arg_tgt o r (PRE: fsp.(precond) mn x arg_src arg_tgt o r), o = ord_top>>).

  (* Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) sk) mds). *)
  (* Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss). *)
  (* Let stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb. *)

  Let mds_mid: list Mod.t := List.map (SMod.to_mid (stb sk)) mds.
  Let mds_tgt: list Mod.t := List.map (SMod.to_tgt stb) mds.

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
    generalize (ModL.sk (Mod.add_list (List.map (SMod.to_mid (stb sk)) mds))). i.
    rewrite ! Mod.add_list_initial_mrs.
    generalize mds. clear. i. induction mds0; auto.
    ss. rewrite IHmds0. auto.
  Qed.

  (* Lemma initial_p_eq: *)
  (*   ModSemL.initial_p_state ms_tgt = ModSemL.initial_p_state ms_mid. *)
  (* Proof. *)
  (*   unfold ModSemL.initial_p_state. extensionality mn. *)
  (*   pose proof sk_eq. *)
  (*   unfold ms_tgt, ms_mid, mds_tgt, mds_mid, ModL.enclose. *)
  (*   unfold mds_mid, mds_tgt in H. rewrite H. *)
  (*   generalize (ModL.sk (Mod.add_list (List.map (SMod.to_mid (stb sk)) mds))). i. *)
  (*   rewrite ! Mod.add_list_initial_mrs. *)
  (*   generalize mds. clear. i. induction mds0; auto. *)
  (*   ss. rewrite eq_rel_dec_correct in *. des_ifs. *)
  (* Qed. *)

  Lemma fns_eq:
    (List.map fst (ModSemL.fnsems (ModL.enclose (Mod.add_list mds_tgt))))
    =
    (List.map fst (ModSemL.fnsems (ModL.enclose (Mod.add_list mds_mid)))).
  Proof.
    pose proof sk_eq. unfold ModL.enclose.
    unfold mds_mid, mds_tgt, ModL.enclose.
    unfold mds_mid, mds_tgt in H. rewrite H.
    generalize (ModL.sk (Mod.add_list (List.map (SMod.to_mid (stb sk)) mds))). i.
    rewrite ! Mod.add_list_fns. rewrite ! List.map_map. f_equal.
    f_equal. extensionality sm. ss. rewrite ! List.map_map. f_equal.
    extensionality fnsb. destruct fnsb as [fn sb]. ss.
  Qed.

  Lemma stb_find_iff_aux fn
    :
      ((<<NONE: alist_find fn (_stb sk) = None>>) /\
       (<<FINDMID: alist_find fn (ModSemL.fnsems ms_mid) = None>>) /\
       (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) = None>>)) \/

      (exists md (f: fspecbody),
          (<<STB: alist_find fn (_stb sk) = Some (f: fspec)>>) /\
          (<<SBTB: alist_find fn sbtb = Some f>>) /\
          (<<FINDMID: alist_find fn (ModSemL.fnsems ms_mid) =
                      Some (transl_all (T:=_)
                              (SModSem.mn (SMod.get_modsem md sk))
                              ∘ fun_to_mid (stb sk) (fsb_body f))>>) /\
          (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) =
                      Some (transl_all (T:=_)
                              (SModSem.mn (SMod.get_modsem md sk))
                              ∘ fun_to_tgt (SModSem.mn (SMod.get_modsem md sk)) (stb sk) f)>>) /\
          (<<MIN: List.In (SModSem.mn (SMod.get_modsem md sk)) (List.map fst ms_tgt.(ModSemL.initial_mrs))>>)).
  Proof.
    unfold ms_mid, ms_tgt, mds_tgt, mds_mid, SMod.to_mid, mds_tgt, SMod.to_tgt.
    rewrite SMod.transl_fnsems. rewrite SMod.transl_fnsems. rewrite SMod.transl_initial_mrs. fold sk.
    unfold _stb at 1 2. unfold sbtb, _sbtb, _mss. rewrite alist_find_map.
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
      ((<<NONE: stb sk fn = None>> \/ (exists fsp, <<FIND: stb sk fn = Some fsp>> /\ <<TRIVIAL: forall mn x arg_src arg_tgt o r (PRE: fsp.(precond) mn x arg_src arg_tgt o r), o = ord_top>>)) /\
       (<<FINDMID: alist_find fn (ModSemL.fnsems ms_mid) = None>>) /\
       (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) = None>>)) \/

      (exists md (f: fspecbody),
          (<<STB: stb sk fn = Some (f: fspec)>>) /\
          (<<SBTB: alist_find fn sbtb = Some f>>) /\
          (<<FINDMID: alist_find fn (ModSemL.fnsems ms_mid) =
                      Some (transl_all (T:=_)
                              (SModSem.mn (SMod.get_modsem md sk))
                              ∘ fun_to_mid (stb sk) (fsb_body f))>>) /\
          (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) =
                      Some (transl_all (T:=_)
                              (SModSem.mn (SMod.get_modsem md sk))
                              ∘ fun_to_tgt (SModSem.mn (SMod.get_modsem md sk)) (stb sk) f)>>) /\
          (<<MIN: List.In (SModSem.mn (SMod.get_modsem md sk)) (List.map fst ms_tgt.(ModSemL.initial_mrs))>>)).
  Proof.
    hexploit (stb_find_iff_aux fn). i. des.
    { left. esplits; et. }
    { right. esplits; et. }
  Qed.

  Let W: Type := (p_state).

  Let r_state: Type := mname -> Σ.

  Let zip_state (mps: p_state) (mrs: r_state): p_state :=
    fun mn => match alist_find mn ms_tgt.(ModSemL.initial_mrs) with
              | Some r => Any.pair (mps mn) (mrs mn)↑
              | None => mps mn
              end.

  Let rsum_minus (mn: mname): r_state -> Σ :=
    fun mrs_tgt => (fold_left (⋅) (List.map (update mrs_tgt mn ε) (List.map fst ms_tgt.(ModSemL.initial_mrs))) ε).

  Let rsum: r_state -> Σ :=
    fun mrs_tgt => (fold_left (⋅) (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε).



  Lemma fold_left_radd (r0 r1: Σ) rl
    :
      fold_left URA.add rl (r0 ⋅ r1) = r0 ⋅ fold_left URA.add rl r1.
  Proof.
    revert r0 r1. induction rl; ss.
    i. rewrite <- URA.add_assoc. rewrite IHrl. auto.
  Qed.

  Lemma fold_left_add (r: Σ) rs
    :
      fold_left URA.add rs r = (fold_left URA.add rs ε) ⋅ r.
  Proof.
    revert r. induction rs; ss.
    { i. rewrite URA.unit_idl. auto. }
    i. rewrite IHrs. rewrite (IHrs (ε ⋅ a)). r_solve.
  Qed.

  (* Lemma rsum_update mn mrs frs r *)
  (*       (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs))) *)
  (*       (IN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs))) *)
  (*   : *)
  (*     rsum (update mrs mn r, frs) = rsum (update mrs mn ε, frs) ⋅ r. *)
  (* Proof. *)
  (*   unfold rsum. rewrite <- URA.add_assoc. rewrite (URA.add_comm _ r). *)
  (*   rewrite URA.add_assoc. f_equal. unfold compose. *)
  (*   rewrite <- (List.map_map fst). rewrite <- (List.map_map fst). revert IN NODUP. *)
  (*   generalize (List.map fst (ModSemL.initial_mrs ms_tgt)) as mds0. i. *)
  (*   cut (forall r0 r1, fold_left URA.add (List.map (update mrs mn r0) mds0) ε ⋅ r1 *)
  (*                      = *)
  (*                      fold_left URA.add (List.map (update mrs mn r1) mds0) ε ⋅ r0). *)
  (*   { i. specialize (H r ε). rewrite URA.unit_id in H. auto. } *)
  (*   i. revert mn r0 r1 IN NODUP. induction mds0; ss. i. *)
  (*   destruct (classic (In mn mds0)). *)
  (*   { clear IN. rewrite (fold_left_add (ε ⋅ update mrs mn r0 a)). *)
  (*     rewrite (fold_left_add (ε ⋅ update mrs mn r1 a)). *)
  (*     rewrite ! URA.unit_idl. rewrite <- URA.add_assoc. rewrite <- URA.add_assoc. *)
  (*     rewrite (URA.add_comm _ r1). rewrite (URA.add_comm _ r0). *)
  (*     rewrite URA.add_assoc. rewrite URA.add_assoc. *)
  (*     inv NODUP. rewrite IHmds0; ss. *)
  (*     f_equal. unfold update. des_ifs. *)
  (*   } *)
  (*   { des; ss. rewrite (fold_left_add (ε ⋅ update mrs mn r0 a)). *)
  (*     rewrite (fold_left_add (ε ⋅ update mrs mn r1 a)). subst. *)
  (*     unfold update at 2 4. des_ifs. *)
  (*     rewrite ! URA.unit_idl. rewrite <- URA.add_assoc. rewrite <- URA.add_assoc. f_equal. *)
  (*     { revert H. clear IHmds0 NODUP. induction mds0; ss. i. *)
  (*       rewrite (fold_left_add (ε ⋅ update mrs mn r0 a)). *)
  (*       rewrite (fold_left_add (ε ⋅ update mrs mn r1 a)). *)
  (*       rewrite IHmds0; auto. f_equal. f_equal. *)
  (*       unfold update. des_ifs; ss. exfalso. eapply H; auto. *)
  (*     } *)
  (*     { eapply URA.add_comm. } *)
  (*   } *)
  (* Qed. *)

  (* Lemma update_same A (mrs: string -> A) mn *)
  (*   : *)
  (*     update mrs mn (mrs mn) = mrs. *)
  (* Proof. *)
  (*   extensionality mn0. unfold update. des_ifs. *)
  (* Qed. *)

  (* Lemma rsum_cons mrs fhd ftl *)
  (*   : *)
  (*     rsum (mrs, fhd::ftl) = fhd ⋅ rsum (mrs, ftl). *)
  (* Proof. *)
  (*   ss. transitivity (fold_left URA.add (List.map (mrs <*> fst) (ModSemL.initial_mrs ms_tgt)) ε *)
  (*                               ⋅ (fhd ⋅ fold_left URA.add ftl ε)). *)
  (*   { f_equal. *)
  (*     generalize fhd. generalize (@URA.unit (GRA.to_URA Σ)). *)
  (*     induction ftl; ss. *)
  (*     { i. r_solve. } *)
  (*     { i. ss. *)
  (*       replace (c ⋅ fhd0 ⋅ a) with ((c ⋅ a) ⋅ fhd0) by r_solve. *)
  (*       rewrite IHftl. r_solve. *)
  (*     } *)
  (*   } *)
  (*   { r_solve. } *)
  (* Qed. *)


  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac mred := repeat (cbn; ired_both).

  Ltac steps := repeat (mred; try _step; des_ifs_safe).





  Let zip_state_get st mrs mn
      (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      zip_state st mrs mn = Any.pair (st mn) (mrs mn)↑.
  Proof.
    unfold zip_state. des_ifs.
    eapply in_map_iff in MIN. des. destruct x. subst.
    eapply alist_find_none in Heq.
    exfalso. eapply Heq. et.
  Qed.

  Let zip_state_mput st mrs mn r
      (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      update (zip_state st mrs) mn (Any.pair (st mn) (Any.upcast r))
      =
      zip_state st (update mrs mn r).
  Proof.
    extensionality mn0.
    unfold update, zip_state. des_ifs.
    eapply in_map_iff in MIN. des. destruct x. subst.
    eapply alist_find_none in Heq.
    exfalso. eapply Heq. et.
  Qed.

  Let rsum_update mn (mrs: r_state) r (mns: list mname) r0
      (MIN: List.In mn mns)
      (NODUP: NoDup mns)
    :
      (fold_left (⋅) (List.map (update mrs mn r) mns) r0) ⋅ (mrs mn)
      =
      (fold_left (⋅) (List.map mrs mns) r0) ⋅ r.
  Proof.
    revert mn mrs r r0 MIN NODUP. induction mns; ss. i.
    inv NODUP. des.
    { subst. rewrite fold_left_add. rewrite (fold_left_add (r0 ⋅ mrs mn)).
      rewrite <- ! URA.add_assoc. f_equal.
      { f_equal. apply map_ext_in. i.
        unfold update. des_ifs. }
      { unfold update. des_ifs. r_solve. }
    }
    { rewrite IHmns; et.
      rewrite fold_left_add. rewrite (fold_left_add (r0 ⋅ mrs a)).
      unfold update. des_ifs. }
  Qed.

  Lemma rsum_minus_update mn0 mn1 mrs r
        (MIN0: List.In mn0 (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (MIN1: List.In mn1 (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      rsum_minus mn0 mrs ⋅ r = rsum_minus mn1 (update mrs mn0 r) ⋅ update mrs mn0 r mn1.
  Proof.
    unfold rsum_minus.
    revert MIN0 MIN1 NODUP. generalize (List.map fst (ModSemL.initial_mrs ms_tgt)). i.
    rewrite rsum_update; et.
    transitivity (fold_left (⋅) (List.map (update (update mrs mn0 ε) mn0 r) l) ε ⋅ (update mrs mn0 ε mn0)).
    { rewrite rsum_update; et. }
    { f_equal.
      { f_equal. f_equal. extensionality mn. unfold update. des_ifs. }
      { unfold update. des_ifs. }
    }
  Qed.

  Local Opaque rsum rsum_minus.



  Let adequacy_type_aux
      (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs))):
    forall RT
           mrs0 frs fr0 ctx0
           st_src0 st_tgt0 (i0: itree (hCallE +' pE +' eventE) RT)
           mn cur
           (ZIP: st_tgt0 = zip_state st_src0 mrs0)
           (CTX: ctx0 = frs ⋅ rsum_minus mn mrs0)
           (RWF: URA.wf (fr0 ⋅ ctx0 ⋅ (mrs0 mn)))

           (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
           (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    ,
      simg (fun '(st_src1, v_src) '(st_tgt1, v_tgt) =>
              exists mrs1 fr1,
                (<<ZIP: st_tgt1 = zip_state st_src1 mrs1>>) /\
                (<<RET: (v_tgt: Σ * Σ * RT) = (frs ⋅ rsum_minus mn mrs1, fr1, v_src)>>) /\
                (<<RWF: URA.wf (fr1 ⋅ (frs ⋅ rsum_minus mn mrs1) ⋅ (mrs1 mn))>>))
           (Ord.from_nat 100%nat)
           (EventsL.interp_Es (ModSemL.prog ms_mid) (transl_all mn (interp_hCallE_mid (stb sk) cur i0)) st_src0)
           (EventsL.interp_Es (ModSemL.prog ms_tgt) (transl_all mn (interp_hCallE_tgt mn (stb sk) cur i0 (ctx0, fr0))) st_tgt0)
  .
  Proof.
    Opaque subevent.
    ginit.
    { i. eapply cpn6_wcompat; eauto with paco. }
    gcofix CIH. i; subst.
    ides i0; try rewrite ! unfold_interp; cbn; mred.
    { steps. esplits; et. }
    { steps. gbase. eapply CIH; [..|M]; Mskip et. ss. }
    rewrite <- bind_trigger. destruct e; cycle 1.
    {
      destruct s; ss.
      {
        destruct p; ss.
        - resub. seal_left. steps. unfold pput. unseal_left. steps.
          erewrite zip_state_get; et. rewrite Any.pair_split. steps.
          gbase. eapply CIH; ss.
          extensionality mn0. unfold update, zip_state. des_ifs.
          exfalso. eapply in_map_iff in MIN. des. destruct x. subst.
          eapply alist_find_none in Heq. et.
        - resub. seal_left. steps. unfold pget. unseal_left. steps.
          erewrite zip_state_get; et. rewrite Any.pair_split. steps.
          gbase. eapply CIH; ss.
      }
      { dependent destruction e.
        - resub. steps. esplits; eauto. steps. gbase. eapply CIH; [..|M]; Mskip et. ss.
        - resub. steps. esplits; eauto. steps. gbase. eapply CIH; [..|M]; Mskip et. ss.
        - resub. steps. gbase. eapply CIH; [..|M]; Mskip et. ss.
      }
    }
    dependent destruction h. resub.
    set (ModSemL.prog ms_mid) as p_mid in *.
    set (ModSemL.prog ms_tgt) as p_tgt in *.
    ss.
    seal_left.

    steps. hexploit (stb_find_iff fn). i. des.
    { rewrite NONE. steps. }
    { rewrite FIND. unfold HoareCall, mput, mget. steps.
      erewrite zip_state_get; et. rewrite Any.pair_split. steps.
      des; clarify. destruct tbr; ss.
      { exfalso. hexploit TRIVIAL; et. i. subst. ss. hexploit x5; ss. }
      seal_right. unseal_left. steps. rewrite FIND. steps. esplits; et.
      steps. esplits; et.
      { destruct cur; ss. hexploit x6; ss. i. subst. ss. }
      steps. rewrite FINDMID. steps.
    }
    unfold HoareCall, mput, mget.

    (*** exploiting both_tau ***)
    rewrite STB. ss. mred. force_r.
    destruct (classic (tbr = true /\ forall mn x arg_src arg_tgt o r (PRE: f.(precond) mn x arg_src arg_tgt o r), o = ord_top)).
    { des. subst. steps.
      erewrite zip_state_get; et. rewrite Any.pair_split. steps.
      hexploit H0; et. i. subst. ss. des. hexploit x2; ss. }
    rename H into TRIVIAL.
    unseal_left. ired_both. rewrite STB. steps. esplit.
    { ii. subst. eapply TRIVIAL; ss. } steps.
    erewrite zip_state_get; et. rewrite Any.pair_split. steps.

    match goal with
    | |- _ ?i_tgt => replace i_tgt with (Ret tt;;; i_tgt)
    end.
    2: { mred. auto. }
    guclo ordC_spec. econs.
    { instantiate (2:=(400+5)%ord).
      rewrite <- OrdArith.add_from_nat. refl. }
    guclo bindC_spec. econs.
    { instantiate (1:= fun '(st_src, o) (_: unit) => st_src = st_src0 /\ o = x2).
      destruct tbr.
      { steps. des. destruct x2; ss.
        { exists n. steps. }
        { exfalso. hexploit x5; ss. }
      }
      { steps. des. splits; auto. symmetry. auto. }
    }
    i. destruct vret_src, vret_tgt. des; subst.

    steps. esplits; eauto. steps. unfold unwrapU.
    rewrite FINDMID. rewrite FINDTGT. rewrite ! bind_ret_l.

    guclo ordC_spec. econs.
    { instantiate (1:=(195+200)%ord). rewrite <- OrdArith.add_from_nat. refl. }
    rename f into fs.
    guclo bindC_spec. econs.

    { instantiate (1:= fun '(st_src1, vret_src) '(st_tgt1, vret_tgt) =>
                         exists (mrs1: r_state) rret,
                           (<<ZIP: st_tgt1 = zip_state st_src1 mrs1>>) /\
                           (<<POST: fs.(postcond) (Some mn) x0 vret_src vret_tgt rret>>) /\
                           (<<RWF: URA.wf (rret ⋅ (c1 ⋅ (frs ⋅ rsum_minus mn mrs1) ⋅ (mrs1 mn)))>>)).
      fold sk. fold sk. set (mn0:=SModSem.mn (SMod.get_modsem md sk)) in *.
      fold Any_tgt in x3.
      unfold fun_to_src, fun_to_tgt, compose. des_ifs. unfold HoareFun, mget, mput.
      rename x3 into PRECOND. rename c0 into rarg.
      steps. exists x0.
      steps. exists varg_src.
      rewrite Any.pair_split. ired_both.
      rewrite Any.upcast_downcast. ired_both. steps.
      eexists (rarg, c1 ⋅ (frs ⋅ rsum_minus mn0 (update mrs0 mn c))).
      steps. erewrite ! zip_state_mput; et.
      erewrite zip_state_get; et.
      rewrite Any.pair_split. steps. rewrite Any.upcast_downcast. steps.
      assert (RWF0: URA.wf (rarg ⋅ (c1 ⋅ (frs ⋅ rsum_minus mn0 (update mrs0 mn c))) ⋅ update mrs0 mn c mn0)).
      { r_wf x. symmetry. eapply rsum_minus_update; et. }
      unshelve esplits; eauto.
      steps. esplits; eauto. steps. unshelve esplits; eauto. steps.
      guclo ordC_spec. econs.
      { instantiate (1:=(73+100)%ord). rewrite <- OrdArith.add_from_nat. refl. }
      guclo bindC_spec. econs.
      { gbase. eapply CIH; ss.
        { instantiate (1:=c1 ⋅ frs). r_solve. }
      }
      { ii. ss. des_ifs_safe. des; ss. clarify.
        steps. rewrite zip_state_get; et.
        rewrite Any.pair_split. steps.
        esplits; ss; et.
        { r_wf x7. symmetry. eapply rsum_minus_update; et. }
      }
    }
    { ii. ss. des_ifs_safe. des. subst.
      steps. eexists (rret, frs ⋅ rsum_minus mn mrs1). steps.
      rewrite zip_state_get; et.
      rewrite Any.pair_split. steps. rewrite Any.upcast_downcast. steps.
      unshelve esplits; et.
      { r_wf RWF0. }
      steps. exists t. steps. unshelve esplits; et.
      steps. gbase. eapply CIH; et.
      { r_wf RWF0. }
    }
  Unshelve.
    all: try (by exact 0).
  Qed.

  Opaque EventsL.interp_Es.

  Let initial_mrs: mname ->  Σ :=
    fun mn => match alist_find mn (List.map (fun md => (SModSem.mn md, SModSem.initial_mr md)) mss) with
              | Some r => r
              | None => ε
              end.

  Lemma initial_p_zip:
    zip_state (ModSemL.initial_p_state ms_mid) initial_mrs =
    ModSemL.initial_p_state ms_tgt.
  Proof.
    admit "ez".
  Qed.

  Lemma initial_rsum_minus mn
    :
      rsum_minus mn initial_mrs ⋅ initial_mrs mn = fold_left URA.add (List.map SModSem.initial_mr mss) ε.
  Proof.
    admit "ez".
  Qed.

  Theorem adequacy_type_t2m
          main_arg_src main_arg_tgt
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb sk "main" = Some main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) None x main_arg_src main_arg_tgt ord_top entry_r>>) /\
               (<<WFR: URA.wf (entry_r ⋅ fold_left (⋅) (List.map SModSem.initial_mr mss) ε)>>) /\
               (<<RET: forall ret_src ret_tgt r
                              (POST: main_fsp.(postcond) None x ret_src ret_tgt r),
                   ret_src = ret_tgt>>)):
    Beh.of_program (ModL.compile_arg (Mod.add_list mds_tgt) main_arg_tgt) <1=
    Beh.of_program (ModL.compile_arg (Mod.add_list mds_mid) (Any.pair ord_top↑ main_arg_src)).
  Proof.
    eapply adequacy_global_itree.
    exists (Ord.from_nat 100%nat). ss.
    ginit.
    { eapply cpn6_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr, ModSemL.initial_itr_arg. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.

    hexploit (stb_find_iff "main"). i. destruct H as [[_ ?]|?]; des; clarify.
    { Local Transparent ModSemL.prog.
      seal_right. ss. unfold ms_mid in FINDMID. rewrite FINDMID. steps.
      Local Opaque ModSemL.prog. }
    rename f into main_fsb. hexploit MAINM; et.
    i. des. rename x into metav.

    unfold assume.
    steps. unfold ModL.wf in *. des.
    assert (NODUP: List.NoDup (map fst ms_tgt.(ModSemL.initial_mrs))).
    { inv WF. rewrite fst_initial_mrs_eq. unfold ms_mid. auto. }
    esplits; et.
    { inv WF. econs; auto. rewrite fns_eq. auto. }
    { rewrite sk_eq. auto. }
    steps. fold ms_tgt ms_mid. rewrite <- initial_p_zip.

    Local Transparent ModSemL.prog. ss.
    unfold Any_src, Any_mid, Any_tgt in *. rewrite FINDTGT. rewrite FINDMID. steps.
    eexists. steps. eexists. steps.
    eexists (entry_r, rsum_minus (SModSem.mn (SMod.get_modsem md sk)) initial_mrs).
    steps. rewrite Any.pair_split.
    unfold mput, mget. steps.
    rewrite zip_state_get; et.
    rewrite Any.pair_split. steps. rewrite ! Any.upcast_downcast. steps.
    assert (RWF: URA.wf (entry_r ⋅ rsum_minus (SModSem.mn (SMod.get_modsem md sk)) initial_mrs ⋅ initial_mrs (SModSem.mn (SMod.get_modsem md sk)))).
    { r_wf WFR. eapply initial_rsum_minus. }
    unshelve esplits; et.
    steps. exists ord_top. steps.
    unshelve esplits; et. steps.

    guclo ordC_spec. econs.
    { instantiate (2:=(_ + _)%ord).
      rewrite <- OrdArith.add_from_nat.
      eapply OrdArith.le_from_nat. refl. }
    guclo bindC_spec. econs.
    { gfinal. right. fold simg.
      eapply adequacy_type_aux; ss.
      { r_solve. }
    }
    i. ss.
    destruct vret_src as [mps_src v_src].
    destruct vret_tgt as [mps_tgt [[? ?] v_tgt]]. des. clarify.
    steps. rewrite zip_state_get; et.
    rewrite Any.pair_split. steps.
    Unshelve. all: try (exact 0).
  Qed.

End CANCEL.
