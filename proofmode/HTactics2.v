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

  Lemma wf_extends
        (x0 x1: Σ)
        (WF: URA.wf x0)
        (EXT: URA.extends x1 x0)
    :
      <<WF: URA.wf x1>>
  .
  Proof. r in EXT. des; clarify. eapply URA.wf_mon; et. Qed.
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
        X (P_src P_tgt: option mname -> X -> Any.t -> Any.t -> iProp) arg_tgt
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

  Lemma hcall_clo2
        (fsp_src: fspec)
        (x_src: shelve__ fsp_src.(meta))

        A (a0: shelve__ A) FR

        (le: A -> A -> Prop) mn r rg a n m mr_src0 mp_src0
        (fsp_tgt: fspec)
        mr_tgt0 mp_tgt0 k_tgt k_src
        fn tbr ord_cur arg_src arg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        fr_src0 fr_tgt0

        (PURE: ord_lt (fsp_src.(measure) x_src) ord_cur /\
               (tbr = true -> is_pure (fsp_src.(measure) x_src)) /\
                 (tbr = false -> (fsp_src.(measure) x_src) = ord_top))

        (POST: forall x_tgt, exists I,
            (<<ACC: current_iPropL (fr_src0 ⋅ mr_src0 ⋅ mr_tgt0) [("I", I)] >>) /\
            (<<UPDATABLE: bi_entails I (OwnT (fr_tgt0) ** OwnT (mr_tgt0) **
                              (fsp_tgt.(precond) (Some mn) x_tgt arg_tgt arg_tgt
                                 ==∗ (FR ** R a0 mp_src0 mp_tgt0 **
                                         (fsp_src.(precond) (Some mn) x_src arg_src arg_tgt: iProp))))>>) /\
            (<<POST: forall (ret_src ret_tgt: Any.t) (mp_src1 mp_tgt1 : Any.t),
            exists J,
              (<<UPDATABLE: bi_entails (FR ** (∃ a1, R a1 mp_src1 mp_tgt1 ** ⌜le a0 a1⌝) **
                                          fsp_src.(postcond) (Some mn) x_src ret_src ret_tgt)
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
                       (HoareCall mn tbr ord_cur fsp_src fn arg_src) fr_src0 >>= k_src)
             (Any.pair mp_tgt0 mr_tgt0↑,
                       (HoareCall mn tbr ord_cur fsp_tgt fn arg_tgt) fr_tgt0 >>= k_tgt)
  .
  Proof.
    subst. unfold HoareCall at 2, mput, mget, assume, guarantee.
    steps.
    rename c into mr_tgt1. rename c0 into ro_tgt. rename c1 into fr_tgt.
    rename x0 into x_tgt. specialize (POST x_tgt). des.
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
      { admit "simple". }
      subst.
      iSpecialize ("A" with "A3").
      iMod "A". iModIntro. iAssumption.
    }
    mUpd "A1". mDesAll.

    inv ACC. rr in IPROP. repeat (autorewrite with iprop in IPROP; autounfold with iprop in IPROP; ss).
    des. subst. rename a1 into mr_src1. rename a3 into ro_src. rename a4 into fr_tgt_. rename a5 into mr_tgt_.
    rename a2 into fr_src.
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
    { etrans; try eassumption. iIntros "H". iDestruct "H" as "[A [B [C _]]]". iFrame. iSplits; et. }
    inv ACC. rr in IPROP. repeat (autorewrite with iprop in IPROP; autounfold with iprop in IPROP; ss).
    des. subst.
    rename a1 into ri_tgt. rename b into jr.
    assert(WF: URA.wf (ri_tgt ⋅ jr ⋅ (fr_tgt ⋅ mr_tgt))).
    { eapply URA.updatable_wf; try apply x6.
      replace (ri_src ⋅ (fr_src ⋅ fr_tgt) ⋅ (mr_tgt ⋅ mr_src')) with
        ((fr_tgt ⋅ mr_tgt) ⋅ (ri_src ⋅ fr_src ⋅ mr_src')) by r_solve.
      replace (ri_tgt ⋅ jr ⋅ (fr_tgt ⋅ mr_tgt)) with ((fr_tgt ⋅ mr_tgt) ⋅ (ri_tgt ⋅ jr)) by r_solve.
      eapply URA.updatable_add; et; try refl. }
    repeat (ired_both; apply sim_itreeC_spec; econs). exists ri_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et.
    { eapply URA.wf_mon. instantiate (1:=jr). r_wf WF. }
    steps.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists ret_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et.
    (* { admit "simple". } *)
    steps.
    eapply SIM.
    econs; et; cycle 1.
    { replace (ri_src ⋅ (fr_src ⋅ fr_tgt) ⋅ (mr_tgt ⋅ mr_src'))
        with ((ri_src ⋅ fr_src ⋅ mr_src') ⋅ (fr_tgt ⋅ mr_tgt)) by r_solve.
      eapply URA.updatable_add; et. refl. }
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
    { admit "simple". }
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

  Local Transparent HoareCall.

  (* Lemma hAPC_both *)
  (*       A (a0: shelve__ A) mp_src0 mp_tgt0 (mr_src0 mr_tgt0: Σ) *)
  (*       mn r rg *)
  (*       k_src k_tgt *)
  (*       _a (le: A -> A -> Prop) *)
  (*       (R: A -> Any.t -> Any.t -> iProp) *)
  (*       (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop) *)
  (*       m n *)
  (*       ctx0 *)
  (*       `{PreOrder _ le} *)

  (*       (* (WF: mk_wf R a0 ((Any.pair mp_src0 mr_src0↑), (Any.pair mp_tgt0 mr_tgt0↑))) *) *)

  (*       rx0 *)
  (*       (* ips Xtra *) *)
  (*       (* (ACC: current_iPropL ctx0 ips) *) *)
  (*       (* (ENTAIL: bi_entails (from_iPropL ips) ((OwnT mr_tgt0) ** (Xtra ∧ Exactly rx))) *) *)
  (*       Xn Invtn Xtra *)
  (*       (ACC: current_iPropL ctx0 [(Invtn, OwnT mr_tgt0); (Xn, (Exactly rx0 Xtra)%I)]) *)
  (*       FR *)
  (*       (ENTAIL: bi_entails Xtra (R a0 mp_src0 mp_tgt0 ** FR)) *)
  (*       (* (WFA: forall a1 mp_src1 mp_tgt1 (mr_src1 mr_tgt1: Σ) (INV: I mr_src1), *) *)
  (*       (*     mk_wf R a1 ((Any.pair mp_src1 mr_src1↑), (Any.pair mp_tgt1 mr_tgt1↑))) *) *)


  (*       stb_src stb_tgt d *)
  (*       (STBINCL: stb_pure_incl stb_tgt stb_src) *)
  (*       (ARG: forall *)
  (*           (mr_src1 mr_tgt1: Σ) (mp_src1 mp_tgt1 : Any.t) a1 *)
  (*           (WLE: le a0 a1) *)
  (*           ctx1 rx1 *)
  (*           (ACC: current_iPropL ctx1 [("INVT", OwnT mr_tgt1); *)
  (*                                     ("X", (Exactly rx1 (R a1 mp_src1 mp_tgt1 ** FR))%I)]), *)
  (*           gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true _a *)
  (*                  (Any.pair mp_src1 mr_src1↑, k_src (ctx1, tt)) *)
  (*                  (Any.pair mp_tgt1 mr_tgt1↑, k_tgt (ctx1 ⋅ rx1, tt))) *)
  (*   : *)
  (*     gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n _a *)
  (*            (Any.pair mp_src0 mr_src0↑, (interp_hCallE_tgt mn stb_src d APC ctx0) >>= k_src) *)
  (*            (Any.pair mp_tgt0 mr_tgt0↑, (interp_hCallE_tgt mn stb_tgt d APC (ctx0 ⋅ rx0)) >>= k_tgt) *)
  (* . *)
  (* Proof. *)
  (*   subst. *)
  (*   unfold APC. steps. force_l. exists x. steps. *)
  (*   deflag. *)
  (*   (* Unset Printing Notations. *) *)
  (*   clear_until x. gen x d ctx0 rx0. gen mp_src0 mp_tgt0 mr_src0 mr_tgt0. gen a0. gen Xtra. gcofix CIH. i. *)
  (*   { *)
  (*     rewrite unfold_APC. ired_both. *)
  (*     force_r. i. force_l. exists x0. *)
  (*     destruct x0. *)
  (*     - steps. eapply gpaco8_mon; et. *)
  (*       { eapply ARG. *)
  (*         { refl. } *)
  (*         clear - ACC ENTAIL. *)
  (*         eapply current_iPropL_pop in ACC; des. *)
  (*         eapply current_iPropL_pop in TL; des. *)
  (*         eapply current_iPropL_nil in TL0. ss. *)
  (*         eapply current_iPropL_push; et. *)
  (*         uipropall. des. clarify. *)
  (*         exploit ENTAIL; try apply HD0. *)
  (*         { eapply wf_extends; et. r. exists (ctx0 ⋅ hdr). instantiate (1:=hdr0).  r_solve. } *)
  (*         { rr in HD1. uipropall. eapply HD1. *)
  (*           { eapply wf_extends; [eapply TL0|]. exists (ctx0 ⋅ hdr). r_solve. } *)
  (*           { auto. } *)
  (*         }             *)
  (*         i; des. clarify. *)
  (*         eapply current_iPropL_push; cycle 1. *)
  (*         { ss. instantiate (1:=a ⋅ b). splits; auto. *)
  (*           rr. uipropall. i. eapply ENTAIL; auto. *)
  (*           rr in HD1. uipropall. eapply HD1; eauto. *)
  (*         } *)
  (*         eapply current_iPropL_nil. *)
  (*         { r_wf TL0. } *)
  (*       } *)
  (*     - *)
  (*       assert(T: exists rf_src rm_src, R a0 mp_src0 mp_tgt0 rm_src /\ FR rf_src /\ rx0 = rf_src ⋅ rm_src). *)
  (*       { clear - ACC ENTAIL. uipropall. *)
  (*         eapply current_iPropL_pop in ACC. des. *)
  (*         eapply current_iPropL_pop in TL. des. *)
  (*         eapply current_iPropL_nil in TL0. ss. *)
  (*         des. clarify. *)
  (*         exploit ENTAIL; try apply HD0. *)
  (*         { eapply wf_extends; et. exists (ctx0 ⋅ hdr). instantiate (1:=hdr0). r_solve. } *)
  (*         { rr in HD1. uipropall. eapply HD1. *)
  (*           { eapply wf_extends; [eapply TL0|]. exists (ctx0 ⋅ hdr). r_solve. } *)
  (*           { auto. } *)
  (*         }             *)
  (*         i; des. clarify. hexploit (ENTAIL rx0). *)
  (*         { eapply wf_extends; eauto. etrans ;eauto. *)
  (*           exists (ctx0 ⋅ hdr). r_solve. *)
  (*         } *)
  (*         { rr in HD1. uipropall. eapply HD1; [|refl]. *)
  (*           { eapply wf_extends; eauto. etrans ;eauto. *)
  (*             exists (ctx0 ⋅ hdr). r_solve. *)
  (*           } *)
  (*         } *)
  (*         { i. des. subst. esplits; eauto. r_solve. } *)
  (*       } *)
  (*       des. subst. *)

  (*       steps. force_l. exists x0. steps. force_l; ss. steps. unfold HoareCall. unfold mput, mget. steps. *)
  (*       des; ss. *)
  (*       assert(STB: stb_src s = Some f). *)
  (*       { eapply STBINCL; et. r. esplits; et. } *)
  (*       force_l. eexists (_, _). steps. rewrite STB. steps. instantiate (1:=t). *)
  (*       unfold HoareCall. unfold mput, mget. steps. *)

  (*       force_l. rename c into mr_tgt1. rename c0 into ro. rename c1 into rf. *)
  (*       exists (ro, rf ⋅ rf_src, rm_src ⋅ mr_tgt1). steps. force_l; ss. *)
  (*       { r_wf _GUARANTEE1. } *)
  (*       steps. force_l. esplits; et. steps. force_l. esplits; et. steps. force_l. esplits; et. *)
  (*       steps. force_l; et. steps. gstep. econs; eauto. *)
  (*       { econs. eapply to_semantic. iIntros "[A B]". iFrame. iStopProof. *)
  (*         uipropall. i. eapply iProp_mono; et. *)
  (*       } *)

  (*       i. inv WF. clarify. steps. *)
  (*       hexploit1 RSRC. *)
  (*       { eapply wf_extends; et. r. exists (c ⋅ rf ⋅ rf_src ⋅ c0). r_solve. } *)
  (*       rename c into ri. rename c0 into ctx1. *)
  (*       rr in RSRC. autounfold with iprop in RSRC; autorewrite with iprop in RSRC. des. clarify. *)
  (*       rename a into rinv. *)
  (*       force_r. exists (ri, ctx1 ⋅ (rinv ⋅ rf_src)). steps. force_r; ss. *)
  (*       { rr in RSRC1. uipropall. red in RSRC1. des. subst. *)
  (*         eapply wf_extends; eauto. exists ctx. r_solve. *)
  (*       } *)
  (*       steps. force_r. esplits. steps. force_r; et. steps. *)

  (*       move CIH at bottom. *)
  (*       deflag. gbase. eapply (CIH _ w1); et. *)
  (*       { i. eapply ARG; try apply ACC0. etrans; et. } *)
  (*       { eapply current_iPropL_push; et. *)
  (*         eapply current_iPropL_push; cycle 1. *)
  (*         { ss. rr. uipropall. splits. *)
  (*           { refl. } *)
  (*           rr. uipropall. i. r in H0. des. subst. *)
  (*           exists (rinv ⋅ ctx), rf_src. esplits. *)
  (*           { r_solve. } *)
  (*           { eapply iProp_mono; [..|eauto]; eauto. *)
  (*             { eapply wf_extends; eauto. exists rf_src. r_solve. } *)
  (*             { exists ctx. r_solve. } *)
  (*           } *)
  (*           { eauto. } *)
  (*         } *)
  (*         eapply current_iPropL_nil. *)
  (*         eapply wf_extends; try apply _ASSUME. *)
  (*         exists (ri ⋅ rf). r_solve. *)
  (*       } *)
  (*   } *)
  (* Unshelve. all: try exact 0. *)
  (* Qed. *)

End MODE.

