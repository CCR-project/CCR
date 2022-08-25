Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef STB SimModSem.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
From Ordinal Require Export Ordinal Arithmetic.
Require Import Red IRed.
Require Import ProofMode.
Require Export HTactics.

Set Implicit Arguments.




Section AUX.
  Context `{Σ: GRA.t}.

  Variant is_simple (fsp: fspec): Prop :=
  | is_simple_intro
      (PRE: forall mn x varg varg_tgt, ⊢ fsp.(precond) mn x varg varg_tgt -* ⌜varg = varg_tgt⌝)
      (POST: forall mn x vret vret_tgt, ⊢ fsp.(postcond) mn x vret vret_tgt -* ⌜vret = vret_tgt⌝)
  .

  Lemma mk_simple_is_simple: forall X DPQ, is_simple (mk_simple (X:=X) DPQ).
  Proof.
    i. econs; ss.
    - i. iIntros "[H %]". ss.
    - i. iIntros "[H %]". ss.
  Qed.
End AUX.



Section MODE.

  Context `{Σ: GRA.t}.

  Let OwnT := Own.

  Local Transparent HoareFun HoareFunArg HoareFunRet HoareCall.

  Variant mk_wf (A: Type)
          (R: A -> Any.t -> Any.t -> iProp)
    : A -> Any.t * Any.t -> Prop :=
  | mk_wf_intro
      a
      mr_src' mr_tgt mp_src mp_tgt
      (RSRC: URA.wf mr_src' -> (R a mp_src mp_tgt) mr_src')
    :
      mk_wf R a ((Any.pair mp_src (mr_tgt ⋅ mr_src')↑), (Any.pair mp_tgt mr_tgt↑))
  .

  Lemma current_iPropL_init
        (res: Σ) Rn
        (WF: URA.wf res)
    :
    current_iPropL res [(Rn, Own res)]
  .
  Proof.
    econs; et; cycle 1.
    { refl. }
    eapply to_semantic; et.
    eapply iPropL_init.
  Qed.

  Lemma current_iPropL_pop
        fmr hd tl
        (P: current_iPropL fmr (hd :: tl))
    :
      exists hdr tlr, <<TL: current_iPropL tlr tl>> ∧ <<HD: hd.2 hdr>> ∧ (URA.updatable fmr (hdr ⋅ tlr))
  .
  Proof.
    rr in P. inv P. destruct hd. ss. unfold from_iPropL in IPROP. fold from_iPropL in IPROP.
    rr in IPROP. rewrite Seal.sealing_eq in *. des. subst. esplits; et.
    - econs; try apply IPROP1; try refl. eapply URA.updatable_wf; et. etrans; et.
      eapply URA.extends_updatable. exists a; r_solve.
  Qed.

  Lemma current_iPropL_push
        fmr hdr
        (hd : string * iProp) tl
        (TL: current_iPropL (fmr) tl)
        (HD: hd.2 hdr)
        (WF: URA.wf (fmr ⋅ hdr))
    :
        <<P: current_iPropL (fmr ⋅ hdr) (hd :: tl)>>
  .
  Proof.
    unfold current_iPropL in *. destruct hd; ss. unfold from_iPropL; fold from_iPropL.
    inv TL.
    econs; et.
    { instantiate (1:=r ⋅ hdr). uipropall. esplits; try apply IPROP; et. r_solve. }
    eapply URA.updatable_add; et. refl.
  Qed.

  Lemma current_iPropL_nil
        fmr
    :
      current_iPropL fmr [] <-> URA.wf fmr
  .
  Proof.
    split; i.
    - rr in H. inv H; et.
    - econs; et; try refl. rr. uipropall.
  Qed.

  Lemma harg_clo2
        A
        mn r rg
        X_src (P_src: option mname -> X_src -> Any.t -> Any.t -> iProp)
        X_tgt (P_tgt: option mname -> X_tgt -> Any.t -> Any.t -> iProp)
        arg_tgt
        mp_src mp_tgt (mr_src mr_tgt: Σ) k_src k_tgt
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (WF: mk_wf R a ((Any.pair mp_src mr_src↑), (Any.pair mp_tgt mr_tgt↑)))
        m n
        (ARG: forall arg_src x_src, exists x_tgt FR,
            <<SEP: bi_entails (R a mp_src mp_tgt ** P_src mn x_src arg_src arg_tgt)
                              (bupd (P_tgt mn x_tgt arg_tgt arg_tgt ** FR))>>
                   /\
            <<SIM: forall mr_src' fr_src fr_tgt
                  (ACC: current_iPropL (fr_src ⋅ (mr_tgt ⋅ mr_src'))
                                       [("FR", FR); ("TF", OwnT fr_tgt); ("TM", OwnT mr_tgt)]),
                gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr true true a
                       (Any.pair mp_src (mr_tgt ⋅ mr_src')↑, k_src (fr_src, ((mn, x_src), arg_src)))
                       (Any.pair mp_tgt mr_tgt↑, k_tgt (fr_tgt, ((mn, x_tgt), arg_tgt)))>>)
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             ((Any.pair mp_src mr_src↑), (HoareFunArg P_src (mn, arg_tgt) >>= k_src))
             ((Any.pair mp_tgt mr_tgt↑), (HoareFunArg P_tgt (mn, arg_tgt) >>= k_tgt))
  .
  Proof.
    inv WF. apply_all_once Any.pair_inj. des. subst. apply_all_once Any.upcast_inj. des; subst. clear_fast.
    unfold HoareFunArg, mput, mget, assume, guarantee.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro x_src.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro arg_src.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro fr_src.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro VALID.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro PRE.
    specialize (ARG arg_src x_src). des.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists x_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists arg_tgt.
    uipropall. exploit RSRC; et.
    { eapply URA.wf_mon. instantiate (1:=fr_src ⋅ mr_tgt). r_wf VALID. }
    i; des.
    specialize (SEP (fr_src ⋅ mr_src')). exploit SEP; et.
    { eapply URA.wf_mon. instantiate (1:=mr_tgt). r_wf VALID. }
    { esplits; try eassumption; try refl; revgoals. r_solve. }
    i; des. subst. rename b into fr_src'. rename a0 into fr_tgt.
    (* rr in x4. des. subst. rename ctx into mr_tgt_spur. *)
    repeat (ired_both; apply sim_itreeC_spec; econs). exists fr_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits.
    { eapply URA.updatable_wf; et.
      replace (fr_src ⋅ (mr_tgt ⋅ mr_src')) with ((fr_src ⋅ mr_src') ⋅ mr_tgt) by r_solve.
      eapply URA.updatable_add; et; try refl.
      etrans; et. eapply URA.extends_updatable.
      exists (fr_src'). r_solve. }
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et.
    ired_both.
    eapply SIM.
    unshelve eassert(T:=@current_iPropL_init (fr_src ⋅ mr_src' ⋅ mr_tgt) "N" _).
    { r_wf VALID. }
    mAssert (#=> (FR ** OwnT fr_tgt ** OwnT mr_tgt)) with "N".
    { iDestruct "N" as "[A B]". iFrame.
      iDestruct (Own_Upd with "A") as "T".
      { r; et. }
      iMod "T". iDestruct "T" as "[A B]". iFrame.
      iStopProof. eapply from_semantic; et.
    }
    mUpd "A". mDesAll. mRename "A1" into "TM". mRename "A2" into "TF". mRename "A" into "FR". ss.
    replace (fr_src ⋅ (mr_tgt ⋅ mr_src')) with (fr_src ⋅ mr_src' ⋅ mr_tgt) by r_solve. ss.
  Qed.

  (*** TODO: update the one in IPM.v ***)
  Lemma from_semantic (a: Σ) (P: iProp') (SAT: P a)
    :
      bi_entails (Own a) (P).
  Proof.
    uipropall. ss. i. eapply iProp_mono; et.
  Qed.

  (*** TODO: move to IPM.v ***)
  Lemma to_semantic_pure: forall (P: Prop), (bi_emp_valid ((⌜P⌝)%I: iProp)) -> P.
  Proof.
    i. rr in H. uipropall. exploit (H ε); eauto.
    { eapply URA.wf_unit. }
    { rr. uipropall. }
    { i. rr in x0. uipropall. }
  Qed.

  Lemma hcall_clo2
        (fsp_src: fspec)

        A (a0: shelve__ A)

        (le: A -> A -> Prop) mn r rg a n m mr_src0 mp_src0
        `{PreOrder _ le}
        (fsp_tgt: fspec)
        mr_tgt0 mp_tgt0 k_tgt k_src
        fn tbr_src tbr_tgt o_src o_tgt arg_src arg_tgt
        (SIMPLE: is_simple fsp_tgt)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        fr_src0 fr_tgt0

        (POST: forall x_tgt (PURE: ord_lt (fsp_tgt.(measure) x_tgt) o_tgt
                                   /\ (tbr_tgt = true -> is_pure (fsp_tgt.(measure) x_tgt))
                                   /\ (tbr_tgt = false -> (fsp_tgt.(measure) x_tgt) = ord_top)),
          exists x_src,
            (<<PURE: ord_lt (fsp_src.(measure) x_src) o_src /\
               (tbr_src = true -> is_pure (fsp_src.(measure) x_src)) /\
                 (tbr_src = false -> (fsp_src.(measure) x_src) = ord_top)>>) /\
          exists I FR,
            (<<ACC: current_iPropL (fr_src0 ⋅ mr_src0 ⋅ mr_tgt0) [("I", I)] >>) /\
            (<<UPDATABLE: bi_entails I (OwnT (fr_tgt0) ** OwnT (mr_tgt0) **
                              (fsp_tgt.(precond) (Some mn) x_tgt arg_tgt arg_tgt
                                 ==∗ (FR ** (∃ a1, R a1 mp_src0 mp_tgt0 ** ⌜le a0 a1⌝) **
                                         (fsp_src.(precond) (Some mn) x_src arg_src arg_tgt: iProp))))>>) /\
            (<<POST: forall (ret_src ret_tgt: Any.t) (mp_src1 mp_tgt1 : Any.t),
            exists J,
              (<<UPDATABLE: (FR ** (∃ a1, R a1 mp_src1 mp_tgt1 ** ⌜le a0 a1⌝) **
                                          fsp_src.(postcond) (Some mn) x_src ret_src ret_tgt) ==∗
                            (fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt ret_tgt ** J)>>) /\
                (<<SIM: forall fr_src1 fr_tgt1 mr_src1 mr_tgt1
                              (ACC: current_iPropL (fr_src1 ⋅ (mr_tgt1 ⋅ mr_src1))
                                                   [("J", J); ("TF", OwnT fr_tgt1); ("TM", OwnT mr_tgt1)]),
                gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true a
                       (Any.pair mp_src1 (mr_tgt1 ⋅ mr_src1)↑, k_src (fr_src1, ret_src))
                       (Any.pair mp_tgt1 mr_tgt1↑, k_tgt (fr_tgt1, ret_tgt))>>)>>))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src0 (mr_tgt0 ⋅ mr_src0)↑,
                       (HoareCall mn tbr_src o_src fsp_src fn arg_src) fr_src0 >>= k_src)
             (Any.pair mp_tgt0 mr_tgt0↑,
                       (HoareCall mn tbr_tgt o_tgt fsp_tgt fn arg_tgt) fr_tgt0 >>= k_tgt)
  .
  Proof.
    subst. unfold HoareCall at 2, mput, mget, assume, guarantee.
    steps.
    rename c into mr_tgt1. rename c0 into ro_tgt. rename c1 into fr_tgt.
    rename x0 into x_tgt. des. specialize (POST x_tgt (conj x3 (conj x0 x4))). des.
    eapply (current_iPropL_entail "I") in ACC; et. unfold alist_add in ACC; ss.
    mDesAll.
    mAssert (Own (fr_tgt0 ⋅ mr_tgt0))%I with "I A1" as "H".
    { iSplitL "I"; iFrame. }
    mAssert _ with "H" as "H".
    { iApply (Own_Upd with "H"); eauto. }
    mUpd "H".
    mAssert _ with "H" as "H".
    { iDestruct "H" as "[[A B] C]". instantiate (1:=_ ** _ ** _).
      iSplitR "A"; try iAssumption. iSplitR "B"; try iAssumption. }
    mDesAll.
    mAssert (_) with "A1".
    { iStopProof. eapply from_semantic; eauto. }
    mAssert (#=> _) with "A A3".
    { assert(x1 = arg_tgt).
      { sym. mAssertPure _; [|eassumption]. inv SIMPLE. iApply PRE; eauto. }
      subst.
      iSpecialize ("A" with "A3").
      iMod "A". iModIntro. iAssumption.
    }
    mUpd "A1". mDesAll.

    inv ACC. rr in IPROP. repeat (autorewrite with iprop in IPROP; autounfold with iprop in IPROP; ss).
    des. subst. rename a2 into mr_src1. rename a3 into fr_src.
    rename a4 into ro_src. rename a5 into fr_tgt_. rename a6 into mr_tgt_.
    unfold HoareCall at 1, mput, mget, assume, guarantee.
    steps.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists (ro_src, (fr_src ⋅ fr_tgt), (mr_tgt1 ⋅ mr_src1)).
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits.
    { replace (fr_src0 ⋅ (mr_tgt0 ⋅ mr_src0)) with (fr_src0 ⋅ mr_src0 ⋅ mr_tgt0) by r_solve. etrans; et.
      rr in IPROP6. rr in IPROP8. des. subst.
      eapply URA.extends_updatable. exists (b3 ⋅ ctx0 ⋅ ctx); r_solve. }
    repeat (ired_both; apply sim_itreeC_spec; econs). esplits; et.
    repeat (ired_both; apply sim_itreeC_spec; econs). esplits; et.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et.
    repeat (ired_both; apply sim_itreeC_spec; econs). econs; et.
    bar.
    i. steps. rename x5 into ri_src. rename t into mp_src2. rename c into mr_src2.
    rename x7 into ret_src. rename vret into ret_tgt.
    inv WF. rewrite Any.pair_split in *. clarify. rewrite Any.upcast_downcast in *. clarify.
    move POST at bottom.
    specialize (POST ret_src ret_tgt mp_src2 mp_tgt). des.
    assert(T: URA.wf (ri_src ⋅ fr_src ⋅ mr_src')).
    { eapply URA.wf_mon; et. instantiate (1:= fr_tgt ⋅ mr_tgt). r_wf x6. }
    assert(ACC:=current_iPropL_init "A" T).
    mAssert (_ ∗ _ ∗ _)%I with "A".
    { iDestruct "A" as "[[A B] C]". iSplitL "A"; try iAssumption. iSplitL "B"; try iAssumption. }
    mDesAll.
    mAssert (_) with "A".
    { iStopProof. eapply from_semantic; et. }
    mAssert (_) with "A1".
    { iStopProof. eapply from_semantic; et. }
    mAssert (_) with "A2".
    { iStopProof. eapply from_semantic; et. eapply RSRC; et. eapply URA.wf_mon.
      instantiate (1:=ri_src ⋅ fr_src ⋅ fr_tgt ⋅ mr_tgt). r_wf x6.
    }
    eapply current_iProp_entail in ACC; cycle 1.
    { etrans; try eassumption. iIntros "H". iDestruct "H" as "[A [B [C _]]]". iFrame. iSplits; et.
      iPureIntro. etrans; eauto. }
    inv ACC. rr in IPROP. repeat (autorewrite with iprop in IPROP; autounfold with iprop in IPROP; ss).
    des. subst.
    rename a2 into ri_tgt. rename b into jr.
    assert(WF: URA.wf (ri_tgt ⋅ jr ⋅ (fr_tgt ⋅ mr_tgt))).
    { eapply URA.updatable_wf; try apply x6.
      replace (ri_src ⋅ (fr_src ⋅ fr_tgt) ⋅ (mr_tgt ⋅ mr_src')) with
        ((fr_tgt ⋅ mr_tgt) ⋅ (ri_src ⋅ fr_src ⋅ mr_src')) by r_solve.
      replace (ri_tgt ⋅ jr ⋅ (fr_tgt ⋅ mr_tgt)) with ((fr_tgt ⋅ mr_tgt) ⋅ (ri_tgt ⋅ jr)) by r_solve.
      eapply URA.updatable_add; et; try refl. etrans; et. }
    repeat (ired_both; apply sim_itreeC_spec; econs). exists ri_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et.
    { eapply URA.wf_mon. instantiate (1:=jr). r_wf WF. }
    steps.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists ret_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et.
    steps.
    eapply SIM.
    econs; et; cycle 1.
    { replace (ri_src ⋅ (fr_src ⋅ fr_tgt) ⋅ (mr_tgt ⋅ mr_src'))
        with ((ri_src ⋅ fr_src ⋅ mr_src') ⋅ (fr_tgt ⋅ mr_tgt)) by r_solve.
      eapply URA.updatable_add. { etrans; et. } refl. }
    { eapply to_semantic; cycle 1.
      { r_wf WF. }
      iIntros "[[A B] [C D]]". iSplitL "B".
      { iStopProof. eapply from_semantic; et. }
      iFrame. iSplitL "A"; iFrame.
    }
  Qed.

  Lemma hret_clo2
        A
        mn r rg n m mp_src mp_tgt (mr_src mr_tgt: Σ) a0
        Xs (Qs: option mname -> Xs -> Any.t -> Any.t -> iProp)
        Xt (Qt: option mname -> Xt -> Any.t -> Any.t -> iProp)
        xs xt vret_src vret_tgt
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (SIMPL: forall mn x vret vret_tgt, ⊢ Qt mn x vret vret_tgt -* ⌜vret = vret_tgt⌝)

        fr_src fr_tgt

        I
        (ACC: current_iPropL (fr_src ⋅ (mr_tgt ⋅ mr_src)) [("I", I)])
        (UPDATABLE:
          bi_entails I (OwnT (fr_tgt) ** OwnT (mr_tgt) **
                             (Qt mn xt vret_tgt vret_tgt
                                 ==∗ ((∃ a, R a mp_src mp_tgt ** ⌜le a0 a⌝)
                                        ** (Qs mn xs vret_src vret_tgt: iProp)))))
        (EQ: forall mr_src mr_tgt a (WLE: le a0 a)
                    (WF: mk_wf R a ((Any.pair mp_src mr_src), (Any.pair mp_tgt mr_tgt))),
            eqr (Any.pair mp_src mr_src) (Any.pair mp_tgt mr_tgt) vret_tgt vret_tgt)
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a0
             (Any.pair mp_src (mr_tgt ⋅ mr_src)↑, (HoareFunRet Qs mn xs (fr_src, vret_src)))
             (Any.pair mp_tgt mr_tgt↑, (HoareFunRet Qt mn xt (fr_tgt, vret_tgt)))
  .
  Proof.
    subst. unfold HoareFunRet, mput, mget, guarantee.
    steps.
    rename c0 into ro_tgt. rename c into mr_tgt0. rename c1 into residue.
    eapply current_iPropL_entail with (Hn:="I") in ACC; et. ss. unfold alist_add in *. ss.
    mDesAll.
    mAssert (#=> (_ ∗ _ ∗ _)) with "I A1".
    { iCombine "I A1" as "A". iDestruct (Own_Upd with "A") as "A"; eauto. iMod "A".
      iDestruct "A" as "[[A B] C]". iSplitL "A"; eauto. iSplitL "B"; eauto. }
    mUpd "A2". mDesAll.
    mAssert _ with "A2".
    { iStopProof. eapply from_semantic; eauto. }
    assert(x = vret_tgt).
    { sym. mAssertPure _; [|eassumption]. iApply SIMPL; et. }
    subst.
    mAssert (#=> _) with "A A4".
    { iSpecialize ("A" with "A4"). iAssumption. }
    mUpd "A2". mDesAll.
    inv ACC. rr in IPROP. repeat (autorewrite with iprop in IPROP; autounfold with iprop in IPROP; ss).
    des. subst.
    rename a1 into mr_src0. rename a2 into ro_src. rename a3 into mr_tgt0_. rename a4 into residue_.
    repeat (ired_both; apply sim_itreeC_spec; econs). esplits.
    repeat (ired_both; apply sim_itreeC_spec; econs). eexists (ro_src, ε, mr_tgt0 ⋅ mr_src0).
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits.
    { etrans; et. eapply URA.extends_updatable.
      rr in IPROP4. des; subst. exists (ctx ⋅ b2 ⋅ residue_). rewrite URA.unit_id. r_solve. }
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    steps. eapply EQ; et. econs; et.
  Qed.

  Lemma current_iPropL_entail_all Hn fmr (l: iPropL) (P: iProp)
        (ACC: current_iPropL fmr l)
        (ENTAIL: from_iPropL l -∗ (bupd P))
    :
      current_iPropL fmr [(Hn, P)].
  Proof.
    eapply current_iProp_upd.
    eapply current_iProp_entail; et.
    unfold from_iPropL at 2. etrans; et. (*** !!! ***)
    iIntros "H". iMod "H". iModIntro. iFrame.
  Qed.

  (* Lemma current_iPropL_merge_all Hn ctx (l: iPropL) *)
  (*   : *)
  (*     current_iPropL ctx l <-> current_iPropL ctx [(Hn, from_iPropL l)]. *)
  (* Proof. *)
  (*   unfold current_iPropL. unfold from_iPropL at 2. *)
  (*   set (from_iPropL l) as x. *)
  (*   set (x ** emp) as y. *)
  (*   assert(x = y). *)
  (*   { subst y. uipropall. extensionality r. apply Axioms.prop_ext. split; i; et. *)
  (*     - esplits; et. { rewrite URA.unit_id; ss. } r. uipropall. *)
  (*     - des. clarify. ss. *)
  (*   Check (from_iPropL l). *)
  (*   Check (from_iPropL l ** emp). *)
  (*   assert((from_iPropL l): iProp = (from_iPropL l ** emp): iProp). *)
  (*   assert(from_iPropL l = from_iPropL l ** emp). *)
  (*   { } *)
  (*   f_equal. *)
  (*   eapply prop_ext. *)
  (*   eapply current_iProp_upd. *)
  (*   eapply current_iProp_entail; et. *)
  (*   unfold from_iPropL at 2. etrans; et. (*** !!! ***) *)
  (* Qed. *)

  Local Transparent APC.

  Definition is_possibly_pure (fsp: fspec): Prop := exists x, is_pure (fsp.(measure) x).

  Definition stb_pure_incl (stb_tgt stb_src: string -> option fspec): Prop :=
    forall fn fsp (FIND: stb_tgt fn = Some fsp) (PURE: is_possibly_pure fsp), stb_src fn = Some fsp
  .

  (*** TODO: stb_pure_incl is too strong. we should use stb_pure_incl2 instead ***)
  Definition stb_pure_incl2 (stb_tgt stb_src: string -> option fspec): Prop :=
    forall fn fsp_tgt (FIND: stb_tgt fn = Some fsp_tgt) x_tgt (PURE: is_pure (fsp_tgt.(measure) x_tgt)),
      exists fsp_src x_src, (<<FIND: stb_src fn = Some fsp_src>>) /\
                              (<<PURE: is_pure (fsp_src.(measure) x_src)>>) /\
                              (<<PRE: forall mn arg_src arg_tgt,
                                  fsp_src.(precond) mn x_src arg_src arg_tgt ==∗
                                                    fsp_tgt.(precond) mn x_tgt arg_src arg_tgt>>) /\
                              (<<POST: forall mn ret_src ret_tgt,
                                  fsp_tgt.(postcond) mn x_tgt ret_src ret_tgt ==∗
                                                    fsp_src.(postcond) mn x_src ret_src ret_tgt>>)
  .

  Local Transparent HoareCall.

  Definition ord_le (o0 o1: ord): Prop :=
    match o0, o1 with
    | ord_pure o0, ord_pure o1 => (o0 <= o1)%ord
    | _, ord_top => True
    | ord_top, _ => False
    end
  .

  Lemma ord_lt_le_lt: forall o0 o1 o2, ord_lt o0 o1 -> ord_le o1 o2 -> ord_lt o0 o2.
  Proof.
    i. destruct o0, o1, o2; ss. eapply Ord.lt_le_lt; eauto.
  Qed.

  Lemma hAPC2
        A (a0: shelve__ A) mp_src0 mp_tgt0 (mr_src0 mr_tgt0: Σ)
        mn r rg
        k_src k_tgt
        _a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        m n
        `{PreOrder _ le}

        fr_src0 fr_tgt0

        FR
        (ACC: current_iPropL (fr_src0 ⋅ (mr_tgt0 ⋅ mr_src0))
                             [("TM", Own mr_tgt0); ("TF", Own fr_tgt0);
                              ("I", (∃ a1, R a1 mp_src0 mp_tgt0 ** ⌜le a0 a1⌝)%I); ("FR", FR)])
        stb_src stb_tgt o_src o_tgt
        (LE: ord_le o_tgt o_src)
        (STBINCL: stb_pure_incl stb_tgt stb_src)
        (SIMPL: forall fn fsp_tgt (IN: stb_tgt fn = Some fsp_tgt), is_simple fsp_tgt)
        (*** TODO: we should be able to remove the above condition. ***)
        (ARG: forall
            (mr_src1 mr_tgt1: Σ) (mp_src1 mp_tgt1 : Any.t)
            fr_src1 fr_tgt1
            (ACC: current_iPropL (fr_src1 ⋅ (mr_tgt1 ⋅ mr_src1))
                                 [("TM", Own mr_tgt1); ("TF", Own fr_tgt1);
                                  ("I", (∃ a1, R a1 mp_src1 mp_tgt1 ∗ ⌜le a0 a1⌝)%I); ("FR", FR)]),
            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true _a
                   (Any.pair mp_src1 (mr_tgt1 ⋅ mr_src1)↑, k_src (fr_src1, tt))
                   (Any.pair mp_tgt1 mr_tgt1↑, k_tgt (fr_tgt1, tt)))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n _a
             (Any.pair mp_src0 (mr_tgt0 ⋅ mr_src0)↑, (interp_hCallE_tgt mn stb_src o_src APC fr_src0) >>= k_src)
             (Any.pair mp_tgt0 mr_tgt0↑, (interp_hCallE_tgt mn stb_tgt o_tgt APC fr_tgt0) >>= k_tgt)
  .
  Proof.
    subst.
    unfold APC. steps. force_l. exists x. steps.
    deflag.
    (* Unset Printing Notations. *)
    clear_until x. gen x o_src o_tgt fr_src0 fr_tgt0. gen mp_src0 mp_tgt0 mr_src0 mr_tgt0. gen a0. gcofix CIH. i.
    {
      rewrite unfold_APC. ired_both.
      force_r. i. force_l. exists x0.
      destruct x0.
      - steps. eapply gpaco8_mon; et.
      - steps. force_l. exists x0. steps. force_l; ss. steps.
        destruct (classic (is_possibly_pure f)); cycle 1.
        { unfold HoareCall. unfold mput, mget. steps. des. contradict H0. r. eauto. }

        assert(STB: stb_src s = Some f).
        { eapply STBINCL; et. }
        force_l. eexists (_, _). steps. rewrite STB. steps. instantiate (1:=t).

        mDesAll.
        eapply hcall_clo2; eauto.
        i. des. exists x_tgt. esplits; eauto; ss.
        { eapply ord_lt_le_lt; eauto. }
        { replace (fr_src0 ⋅ mr_src0 ⋅ mr_tgt0) with (fr_src0 ⋅ (mr_tgt0 ⋅ mr_src0)) by r_solve.
          eapply current_iProp_entail; eauto.
          iIntros "[A [B [C [D _]]]]". iFrame. iIntros "H". iFrame. iModIntro.
          iSplitL "D"; try iAssumption. iSplits; eauto. }
        i.
        esplits; eauto.
        { iIntros "[[A B] C]".
          iAssert (⌜ret_src = ret_tgt⌝)%I as "%".
          { exploit SIMPL; eauto. intro T. inv T. iApply POST; et. }
          subst. iFrame. iCombine "A B" as "A". eauto. }
        i. steps.
        move CIH at bottom.
        deflag. gbase. mDesAll. eapply (CIH); et.
        { eapply current_iProp_entail; eauto. iIntros "[A [B [C [D _]]]]". iFrame. iSplits; eauto. }
    }
  Unshelve. all: try exact 0.
  Qed.

End MODE.

