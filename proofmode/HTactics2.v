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

  Definition OwnT := Own.

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
                  (ACC: current_iPropL (fr_src ⋅ mr_src' ⋅ mr_tgt)
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

        fr_src0 fr_tgt0 I
        (ACC: current_iPropL (fr_src0 ⋅ mr_src0 ⋅ mr_tgt0) [("I", I)])

        (UPDATABLE: forall x_tgt,
           bi_entails I (OwnT (fr_tgt0) ** OwnT (mr_tgt0) **
                              (fsp_tgt.(precond) (Some mn) x_tgt arg_tgt arg_tgt
                                 ==∗ (FR ** R a0 mp_src0 mp_tgt0 **
                                         (fsp_src.(precond) (Some mn) x_src arg_src arg_tgt: iProp)))))

        (PURE: ord_lt (fsp_src.(measure) x_src) ord_cur /\
               (tbr = true -> is_pure (fsp_src.(measure) x_src)) /\
                 (tbr = false -> (fsp_src.(measure) x_src) = ord_top))

        (POST: forall (ret_tgt: Any.t) (mr_src1 mr_tgt1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (ret_src: Any.t)
                      (WLE: le a0 a1)
                      fr_src1 fr_tgt1 x_tgt,
            exists J,
              (<<UPDATABLE: bi_entails (FR ** OwnT fr_tgt1 ** OwnT mr_tgt1 ** R a1 mp_src1 mp_tgt1 **
                                          fsp_src.(postcond) (Some mn) x_src ret_src ret_tgt)
                                      (OwnT fr_tgt1 ** OwnT mr_tgt1 **
                                            fsp_tgt.(postcond) (Some mn) x_tgt ret_src ret_tgt ** J)>>) /\
                <<SIM: forall (ACC: current_iPropL (fr_src1 ⋅ mr_src1) [("J", J)]),
                gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true a
                       (Any.pair mp_src1 (mr_src1 ⋅ mr_tgt1)↑, k_src (fr_src1, ret_src))
                       (Any.pair mp_tgt1 mr_tgt1↑, k_tgt (fr_tgt1, ret_tgt))>>)
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
    rename x0 into x_tgt. specialize (UPDATABLE x_tgt).
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
    mAssert (#=> _) with "A1".
    { iStopProof. eapply from_semantic. eauto. }
    mUpd "A3".
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
    specialize (POST ret_tgt mr_src' mr_tgt mp_src2 mp_tgt w1 ret_src WLE fr_src fr_tgt x_tgt). des.
    assert(ACC:=current_iPropL_init "A" x6).
    mAssert (_ ∗ _ ∗ _ ∗ _ ∗ _)%I with "A".
    { iDestruct "A" as "[[A [B C]] [D E]]".
      iSplitL "A"; try iAssumption. iSplitL "B"; try iAssumption.
      iSplitL "C"; try iAssumption. iSplitL "D"; try iAssumption. }
    mDesAll.
    mAssert (#=> _) with "A1".
    { iStopProof. eapply from_semantic; et. }
    mAssert (#=> _) with "A".
    { iStopProof. eapply from_semantic; et. }
    mAssert (#=> _) with "A4".
    { iStopProof. eapply from_semantic; et. eapply RSRC; et. eapply URA.wf_mon.
      instantiate (1:=ri_src ⋅ fr_src ⋅ fr_tgt ⋅ mr_tgt). r_wf x6.
    }
    mUpd "A". mUpd "A5". mUpd "A1".
    eapply current_iProp_entail in ACC; cycle 1.
    { etrans; try eassumption. iIntros "H". iDestruct "H" as "[A [B [C [D [E _]]]]]". iFrame. }
    inv ACC. rr in IPROP. repeat (autorewrite with iprop in IPROP; autounfold with iprop in IPROP; ss).
    des. subst.
    clears fr_tgt_; clear fr_tgt_. rename a3 into fr_tgt_.
    clears mr_tgt_; clear mr_tgt_. rename b1 into mr_tgt_.
    rename b0 into ri_tgt. rename b into jr.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists ri_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et.
    { eapply URA.updatable_wf; et. etrans; et. rr in IPROP10. rr in IPROP11.
      autorewrite with iprop in *. rr in IPROP10. rr in IPROP11. des; subst.
      eapply URA.extends_updatable. exists (jr ⋅ ctx ⋅ ctx0). r_solve. }
    steps.
    repeat (ired_both; apply sim_itreeC_spec; econs). esplits; et.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et.
    steps.
    TTTTTTTTTTTTTTTTTTT
    eapply SIM.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et.
    
      et. }
    mDesAll.
    assert(ACC: current_iPropL [("I", ((((FR ** OwnT fr_tgt) ** OwnT mr_tgt) ** R w1 mp_src2 mp_tgt) **
                postcond fsp_src (Some mn) x_src ret_src ret_tgt))]).
    ss.
    exploit POST; et. i; des.
    repeat (ired_both; apply sim_itreeC_spec; econs). econs; et.
    { econs; et. }
    {
      eapply URA.updatabe_add; et.
    steps.


    eauto.
    mDestruct (Own_Upd with "H") as "H".
    assert (exists mr_src1 ro_src fr_src1,
               (<<UPDATABLE: URA.updatable (fr_src0 ⋅ mr_src0 ⋅ mr_tgt0)
                                           (mr_tgt1 ⋅ mr_src1 ⋅ ro_src ⋅ fr_src1)>>) /\
               (<<RSRC: R a0 mp_src0 mp_tgt0 mr_src1>>) /\
               (<<FRS: FR fr_src1>>) /\
               (<<PRE: fsp_src.(precond) (Some mn) x_src arg_src arg_tgt ro_src>>)
           ).
    { clear - ACC UPDATABLE x x1 x2 x3.
      eapply current_iPropL_pop in ACC; des.
      eapply current_iPropL_pop in TL; des.
      eapply current_iPropL_nil in TL0. ss.
      specialize (UPDATABLE x0).
      rr in HD0. autorewrite with iprop in HD0. des; clarify. r in HD1. autorewrite with iprop in HD1. des; clarify.
      uipropall. exploit UPDATABLE; swap 1 2.
      { esplits; et.
        { rr in HD1. uipropall. eapply HD1; [|refl].
          eapply wf_extends; try apply x.
          exists (ro_tgt ⋅ fr_tgt ⋅ ctx0 ⋅ mr_tgt1). r_solve.
        }
        { rr. uipropall. }
      }
      { eapply wf_extends; et. r. exists (fr_tgt ⋅ ctx0 ⋅ mr_tgt1). instantiate (1:=ε). r_solve. }
      { instantiate (1:= fr_tgt ⋅ ctx0 ⋅ mr_tgt1). r_wf x. }
      i; des. clarify.
      rr in x8. uipropall. des; ss.
      esplits; et.
      { eapply wf_extends; et. r. exists b. r_solve. }
    }

    unfold HoareCall at 1, mput, mget, assume, guarantee.
    repeat (ired_both; apply sim_itreeC_spec; econs). eexists (_, _, _).
    intro x_src.
    ired_both. apply sim_itreeC_spec. econs.
    hexploit (WEAKER x). i. des.
    assert (exists mr_src0' rarg_src fr_src0',
               (<<UPDATABLE: URA.updatable (fr0 ⋅ mr_src0) (mr_src0' ⋅ (rarg_src ⋅ fr_src0'))>>) /\
               (<<RSRC: R a0 mp_src0 mp_tgt0 mr_src0'>>) /\
               (<<FRS: FR fr_src0'>>) /\
               (<<PRE: fsp0.(precond) (Some mn) x_tgt varg_src varg_tgt rarg_src>>)).
    { inv ACC. uipropall.
      hexploit UPDATABLE; try apply IPROP.
      { eapply URA.updatable_wf; et. }
      i. des. subst.
      hexploit PRE; et. i. uipropall.
      hexploit (H b); et.
      { eapply URA.updatable_wf; et. etrans; et. etrans; et. eapply URA.extends_updatable.
        exists (a2 ⋅ b0). r_solve. }
      i; des.
      esplits; et.
      etrans; et. etrans; et.
      replace (b0 ⋅ (r1 ⋅ a2)) with (b0 ⋅ a2 ⋅ r1) by r_solve.
      eapply URA.updatable_add; et. rewrite URA.add_comm; ss.
    }
    des. exists (rarg_src, fr_src0', mr_src0').
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits.
    { replace (rarg_src ⋅ fr_src0' ⋅ mr_src0') with (mr_src0' ⋅ (rarg_src ⋅ fr_src0')) by r_solve. ss. }
    repeat (ired_both; apply sim_itreeC_spec; econs). exists x_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists varg_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    { r in MEASURE. des_ifs; ss; des_ifs. eapply Ord.le_lt_lt; et. }
    { i. spc PURE0. r in MEASURE. des_ifs; ss; des_ifs. }
    { i. spc PURE1. r in MEASURE. des_ifs; ss; des_ifs. }
    repeat (ired_both; apply sim_itreeC_spec; econs).
    { econs; eauto. }
    i. repeat (ired_both; apply sim_itreeC_spec; econs). i.
    repeat (ired_both; apply sim_itreeC_spec; econs). inv WF.
    repeat (ired_both; apply sim_itreeC_spec; econs). i.
    repeat (ired_both; apply sim_itreeC_spec; econs). i.
    repeat (ired_both; apply sim_itreeC_spec; econs). i.
    ired_both. eapply POST; eauto. hexploit POST0. i.
    uipropall. hexploit (H x0).
    { eapply URA.wf_extends; et. exists (fr_src0' ⋅ mr_src). r_solve. }
    { eassumption. }
    i; des. econs.
    { cbn. esplits; et. eapply RSRC0; et. eapply URA.wf_extends; et. exists (fr_src0' ⋅ x0). r_solve. }
    { ss. }
    replace (fr_src0' ⋅ mr_src ⋅ r1) with (r1 ⋅ fr_src0' ⋅ mr_src) by r_solve.
    rewrite <- ! URA.add_assoc.
    eapply URA.updatable_add; et. refl.
  Qed.

  Lemma harg_clo
        A Rn Invsn Invtn
        mn r rg
        X (P: option mname -> X -> Any.t -> Any.t -> iProp) varg
        mp_src mp_tgt (mr_src mr_tgt: Σ) f_tgt k_src
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (WF: mk_wf R a ((Any.pair mp_src mr_src↑), (Any.pair mp_tgt mr_tgt↑)))
        m n
        (ARG:
           forall x varg_src ctx
                  (ACC: current_iPropL ctx [(Rn, P mn x varg_src varg);
                                           (Invsn, R a mp_src mp_tgt);
                                           (Invtn, OwnT mr_tgt)]),
             gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr true n a
                    (Any.pair mp_src mr_src↑, k_src (ctx, ((mn, x), varg_src)))
                    (Any.pair mp_tgt mr_tgt↑, f_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             ((Any.pair mp_src mr_src↑), (HoareFunArg P (mn, varg) >>= k_src))
             ((Any.pair mp_tgt mr_tgt↑), f_tgt)
  .
  Proof.
    inv WF.
    unfold HoareFunArg, mput, mget, assume, guarantee.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro x.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro varg_src.
    repeat (ired_both; apply sim_itreeC_spec; econs). intros (rarg_src, ctx).
    repeat (ired_both; apply sim_itreeC_spec; econs).
    repeat (ired_both; apply sim_itreeC_spec; econs). intro VALID.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro ord_cur.
    repeat (ired_both; gstep; econs). i.
    eapply Any.pair_inj in H2. des; clarify. eapply Any.upcast_inj in H0. des; clarify.
    eapply Any.pair_inj in H1. des; clarify. eapply Any.upcast_inj in H0. des; clarify.
    ired_both. eapply ARG; et.
    red. econs.
    { instantiate (1:=rarg_src ⋅ mr_src). r_wf VALID. }
    { ss. red. rr.
      autorewrite with iprop; ss. esplits; et.
      assert(T: URA.wf mr_src).
      { eapply URA.wf_mon. instantiate (1:=(ctx ⋅ rarg_src)). r_wf VALID. }
      spc RSRC.
      clear - RSRC T VALID. unfold OwnT in *.
      uipropall. des. clarify. esplits; et.
      { rewrite URA.unit_id; ss. }
      { rr. uipropall. }
    }
    Unshelve. all: try exact 0.
  Qed.

  Definition Exactly (r0: Σ) (Xtra: iProp): iProp :=
    (Own r0 ∧ (⌜Entails (Own r0) Xtra⌝))%I.
  
  Hint Unfold Exactly: iprop.

  Lemma harg_clo_tgt
        A Xn Xtra Rn Invtn mp_tgt mr_tgt
        Invtn' Xn'
        mn r rg
        X (P: option mname -> X -> Any.t -> Any.t -> iProp) varg
        mp_src (mr_src: Σ) f_src k_tgt
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        m n
        ctx x varg_tgt
        (ACC: current_iPropL ctx [(Rn, P mn x varg_tgt varg); (Invtn, OwnT mr_tgt); (Xn, Xtra)])
        (ARG: forall
            rx
            (ACC: current_iPropL ctx [(Invtn', OwnT mr_tgt); (Xn', Exactly rx Xtra)]),
            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m true a
                   (Any.pair mp_src mr_src↑, f_src)
                   (Any.pair mp_tgt mr_tgt↑, k_tgt (ctx ⋅ rx, ((mn, x), varg_tgt))))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src mr_src↑, f_src)
             (Any.pair mp_tgt mr_tgt↑, (HoareFunArg P (mn, varg) >>= k_tgt))
  .
  Proof.
    subst.
    unfold HoareFunArg, mput, mget, assume, guarantee. des.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists x.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists varg_tgt.
    eapply current_iPropL_pop in ACC. des.
    eapply current_iPropL_pop in TL. des.
    eapply current_iPropL_pop in TL0. des. ss. clear_fast.
    eapply current_iPropL_nil in TL. rename hdr into rarg_src. rename hdr0 into rinv. rename hdr1 into rx.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists (rarg_src, (ctx ⋅ rx)).
    repeat (ired_both; apply sim_itreeC_spec; econs). esplits.
    { clear - TL HD0. rr in HD0. uipropall. rr in HD0. des; clarify.
      eapply wf_extends; et. exists ctx0. r_solve. }
    repeat (ired_both; apply sim_itreeC_spec; econs). eexists; et.
    ired_both. eapply ARG.
    eapply current_iPropL_push; et.
    eapply current_iPropL_push; et.
    { instantiate (1:=rx). eapply current_iPropL_nil; et.
      eapply wf_extends; et. exists rarg_src. r_solve.
    }
    { cbn. rr. uipropall. splits; [refl|].
      rr. uipropall. i. eapply iProp_mono; eauto.
    }
  Unshelve. all: try exact 0.
  Qed.

  Lemma current_iPropL_entail_all Hn ctx (l: iPropL) (P: iProp)
        (ACC: current_iPropL ctx l)
        (ENTAIL: from_iPropL l -∗ (bupd P))
    :
      current_iPropL ctx [(Hn, P)].
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

  Lemma harg_clo_tgt'
        A Xn Invtn Xtra mp_tgt mr_tgt
        mn r rg
        X (P: option mname -> X -> Any.t -> Any.t -> iProp) varg
        mp_src (mr_src: Σ) f_src k_tgt
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        m n
        ctx x varg_tgt ips
        (ACC: current_iPropL ctx ips)
        (ENTAIL: bi_entails (from_iPropL ips) (bupd (P mn x varg_tgt varg ** OwnT mr_tgt ** Xtra)))
        (ARG: forall
            rx
            (ACC: current_iPropL ctx [(Invtn, OwnT mr_tgt); (Xn, Exactly rx Xtra%I)]),
            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m true a
                   (Any.pair mp_src mr_src↑, f_src)
                   (Any.pair mp_tgt mr_tgt↑, k_tgt (ctx ⋅ rx, ((mn, x), varg_tgt))))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src mr_src↑, f_src)
             (Any.pair mp_tgt mr_tgt↑, (HoareFunArg P (mn, varg) >>= k_tgt))
  .
  Proof.
    eapply current_iPropL_entail_all with (Hn:="A") in ACC; et.
    mDesAll.
    mAssert _ with "A1". { iAssumption. }
    mAssert _ with "A2". { iAssumption. }
    mAssert _ with "A". { iAssumption. }
    eapply harg_clo_tgt; et.
  Qed.

  Lemma hret_clo_both
        A (a: shelve__ A)
        mn r rg n m mp_src mp_tgt (mr_src mr_tgt: Σ) a0
        Xs (Qs: option mname -> Xs -> Any.t -> Any.t -> iProp)
        Xt (Qt: option mname -> Xt -> Any.t -> Any.t -> iProp)
        xs xt vret_src vret_tgt
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)

        ctx rx
        Invtn Xn Xtra
        (ACC: current_iPropL ctx [(Invtn, OwnT mr_tgt); (Xn, Exactly rx Xtra)])

        (WLE: le a0 a)

        (UPDATABLE: forall vret_tgt_tgt,
           bi_entails ((Qt mn xt vret_tgt vret_tgt_tgt: iProp) ** Xtra)
                      (bupd (R a mp_src mp_tgt ** (Qs mn xs vret_src vret_tgt: iProp))))

        (EQ: forall (mr_src1 mr_tgt1: Σ) (WLE: le a0 a) vret_tgt_tgt
                    (WF: mk_wf R a (Any.pair mp_src mr_src1↑, Any.pair mp_tgt mr_tgt1↑)),
                    bi_entails (Qt mn xt vret_tgt vret_tgt_tgt)
            (⌜eqr (Any.pair mp_src mr_src1↑) (Any.pair mp_tgt mr_tgt1↑) vret_tgt vret_tgt_tgt⌝)%I)
        (* (EQ: forall (mr_src1 mr_tgt1: Σ) (WLE: le a0 a) vret_tgt_tgt *)
        (*             (QT: exists rq, Qt mn xt vret_tgt vret_tgt_tgt rq) *)
        (*             (WF: mk_wf R a (Any.pair mp_src mr_src1↑, Any.pair mp_tgt mr_tgt1↑)), *)
        (*     eqr (Any.pair mp_src mr_src1↑) (Any.pair mp_tgt mr_tgt1↑) vret_tgt vret_tgt_tgt) *)
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a0
             (Any.pair mp_src mr_src↑, (HoareFunRet Qs mn xs (ctx, vret_src)))
             (Any.pair mp_tgt mr_tgt↑, (HoareFunRet Qt mn xt (ctx ⋅ rx, vret_tgt)))
  .
  Proof.
    subst. unfold HoareFunRet, mput, mget, guarantee.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists vret_tgt.
    steps.
    repeat (ired_both; apply sim_itreeC_spec; econs).
    rename c0 into mr_tgt1.
    assert (exists mr_src1 rret_src,
               (<<UPDATABLE: URA.wf (ctx ⋅ (mr_tgt1 ⋅ mr_src1 ⋅ rret_src))>>) /\
               (<<RSRC: R a mp_src mp_tgt mr_src1>>) /\
               (<<PRE: Qs mn xs vret_src vret_tgt rret_src>>)).
    { clear - ACC UPDATABLE x0 x1. red in ACC. inv ACC.
      rename x into vret_tgt_tgt. rename c into rt.
      specialize (UPDATABLE vret_tgt_tgt).
      unfold from_iPropL in IPROP.
      uipropall. des. clarify.
      rename a1 into rx0.
      hexploit (UPDATABLE (rt ⋅ rx)); et.
      { eapply wf_extends; try apply x0. r. exists (ctx ⋅ mr_tgt1). r_solve. }
      { esplits; eauto. rr in IPROP4. uipropall. eapply IPROP4; eauto.
        { eapply wf_extends; try apply x0. r. exists (ctx ⋅ mr_tgt1 ⋅ rt). r_solve. }
        { refl. }
      }
      { instantiate (1:=ctx ⋅ mr_tgt1). r_wf x0. }
      i. des. subst. esplits; [|eauto|eauto].
      { r_wf H. }
    }
    des. exists (rret_src, mr_src1 ⋅ mr_tgt1).
    steps.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits.
    { r_wf UPDATABLE0. }
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    repeat (ired_both; apply sim_itreeC_spec; econs).
    exploit EQ; et.
    { econs; et. ii. unfold OwnT. uipropall. esplits; et. refl. }
    i. uipropall. exploit x3; try apply x1; et.
    { eapply wf_extends; try apply x0. exists (ctx ⋅ rx ⋅ mr_tgt1). r_solve. }
    i. rr in x4. uipropall. et.
  Unshelve. all: ss.
  Qed.

  Definition HoareCallPre
             (mn: mname)
             (tbr: bool)
             (ord_cur: ord)
             (fsp: fspec):
    gname -> Any.t -> Σ -> (itree Es) _ :=
    fun fn varg_src ctx =>
      '(rarg, fr, mr) <- trigger (Choose (Σ * Σ * Σ));;
      _ <- mput mr;;
      _ <- guarantee(URA.wf (rarg ⋅ fr ⋅ ctx ⋅ mr));;

      x <- trigger (Choose fsp.(meta));; varg_tgt <- trigger (Choose Any.t);;
      let ord_next := measure fsp x in
      _ <- guarantee(fsp.(precond) (Some mn) x varg_src varg_tgt rarg);;

      _ <- guarantee(ord_lt ord_next ord_cur /\ (tbr = true -> is_pure ord_next) /\ (tbr = false -> ord_next = ord_top));;
      Ret (x, fr, varg_tgt)
  .

  Definition HoareCallPost
             X
             (mn: mname)
             (tbr: bool)
             (ord_cur: ord)
             (Q: option string → X → Any.t → Any.t → Σ → Prop)
             (vret_tgt: Any.t)
             (x: X)
             (fr: Σ):
    itree Es (Σ * Any.t) :=
      '(rret, ctx) <- trigger (Take (Σ * Σ));;
      mr <- mget;;
      _ <- assume(URA.wf (rret ⋅ fr ⋅ ctx ⋅ mr));;

      vret_src <- trigger (Take Any.t);;
      _ <- assume(Q (Some mn) x vret_src vret_tgt rret);;

      Ret (ctx, vret_src) (*** return to body ***)
  .

  Lemma HoareCall_parse
        (mn: mname)
        (tbr: bool)
        (ord_cur: ord)
        (fsp: fspec)
        (fn: gname)
        (varg_src: Any.t)
        (ctx: Σ):
      HoareCall mn tbr ord_cur fsp fn varg_src ctx =
      '(x, fr, varg_tgt) <- HoareCallPre mn tbr ord_cur fsp fn varg_src ctx;;
      vret_tgt <- trigger (Call fn varg_tgt);;
      HoareCallPost mn tbr ord_cur fsp.(postcond) vret_tgt x fr
  .
  Proof.
    unfold HoareCall, HoareCallPre, HoareCallPost. grind.
  Qed.

  Lemma hcall_clo_ord_weaken'
        fsp_src (x_src: shelve__ fsp_src.(meta))
        fsp_tgt

        A (a0: shelve__ A) FR

        (le: A -> A -> Prop) mn r rg _a n m mp_src0 mp_tgt0 (mr_src0 mr_tgt0: Σ)
        k_tgt k_src
        fn tbr_src tbr_tgt ord_cur_src ord_cur_tgt varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)


        ctx0 rx
        Invtn Xn Xtra
        (ACC: current_iPropL ctx0 [(Invtn, OwnT mr_tgt0); (Xn, (Exactly rx Xtra)%I)])

        (UPDATABLE: forall x_tgt,
           bi_entails (Xtra ** (fsp_tgt.(precond) (Some mn) x_tgt varg_tgt varg_tgt: iProp) **
                            ⌜ord_lt (measure fsp_tgt x_tgt) ord_cur_tgt
                             ∧ (tbr_tgt = true → is_pure (measure fsp_tgt x_tgt))
                             ∧ (tbr_tgt = false → measure fsp_tgt x_tgt = ord_top)⌝)
                      (bupd (FR ** R a0 mp_src0 mp_tgt0 **
                                (fsp_src.(precond) (Some mn) x_src varg_src varg_tgt: iProp) **
                                ⌜ord_lt (measure fsp_src x_src) ord_cur_src
                             ∧ (tbr_src = true → is_pure (measure fsp_src x_src))
                             ∧ (tbr_src = false → measure fsp_src x_src = ord_top)⌝
        )))

        (SIMPLE: forall x_tgt varg_tgt_tgt,
            (bi_entails ((precond fsp_tgt (Some mn) x_tgt varg_tgt varg_tgt_tgt): iProp) (⌜varg_tgt = varg_tgt_tgt⌝%I)))

        (POST: forall (vret_tgt : Any.t) (mr_src1 mr_tgt1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      ctx1 fr_tgt x_tgt
                      (* (ACC: current_iProp ctx1 (FR ** OwnT fr_tgt ** OwnT mr_tgt1 *)
                      (*                              ** R a1 mp_src1 mp_tgt1 ** fsp_src.(postcond) (Some mn) x_src vret_src vret_tgt)) *)
                      (ACC: current_iPropL ctx1 [("FR", FR); ("FRT", OwnT fr_tgt); ("INV", R a1 mp_src1 mp_tgt1 ** OwnT mr_tgt1);
                                                ("POST", fsp_src.(postcond) (Some mn) x_src vret_src vret_tgt)])
          ,
                gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true _a
                       (Any.pair mp_src1 mr_src1↑, k_src (ctx1, vret_src))
                       (Any.pair mp_tgt1 mr_tgt1↑, HoareCallPost mn tbr_tgt ord_cur_tgt fsp_tgt.(postcond) vret_tgt x_tgt fr_tgt >>= k_tgt)
        )
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n _a
             (Any.pair mp_src0 mr_src0↑, (HoareCall mn tbr_src ord_cur_src fsp_src fn varg_src) ctx0 >>= k_src)
             (Any.pair mp_tgt0 mr_tgt0↑, (HoareCall mn tbr_tgt ord_cur_tgt fsp_tgt fn varg_tgt) (ctx0 ⋅ rx) >>= k_tgt)
  .
  Proof.
    subst. rewrite ! HoareCall_parse. unfold HoareCallPre, mput, mget, assume, guarantee.
    steps.
    rename c into mr_tgt1. rename c0 into ro_tgt. rename c1 into fr_tgt.
    assert(x1 = varg_tgt).
    { exploit SIMPLE; et. intros T. uipropall.
      exploit (T ro_tgt); et.
      { eapply wf_extends; try apply x. r. exists (fr_tgt ⋅ ctx0 ⋅ rx ⋅ mr_tgt1). r_solve.  }
      intro U. rr in U. uipropall.
    }
    subst.
    assert (exists mr_src1 ro_src fr_src,
               (<<UPDATABLE: URA.wf (ctx0 ⋅ (mr_tgt1 ⋅ mr_src1 ⋅ ro_src ⋅ fr_src ⋅ fr_tgt))>>) /\
               (<<RSRC: R a0 mp_src0 mp_tgt0 mr_src1>>) /\
               (<<FRS: FR fr_src>>) /\
               (<<PRE: fsp_src.(precond) (Some mn) x_src varg_src varg_tgt ro_src>>) ∧
               (<<MEASURE: ord_lt (measure fsp_src x_src) ord_cur_src ∧
                           (tbr_src = true → is_pure (measure fsp_src x_src)) ∧
                           (tbr_src = false → measure fsp_src x_src = ord_top)>>)
           ).
    { clear - ACC UPDATABLE x x0 x2 x3.
      eapply current_iPropL_pop in ACC; des.
      eapply current_iPropL_pop in TL; des.
      eapply current_iPropL_nil in TL0. ss.
      specialize (UPDATABLE x0).
      rr in HD0. autorewrite with iprop in HD0. des; clarify. r in HD1. autorewrite with iprop in HD1. des; clarify.
      uipropall. exploit UPDATABLE; swap 1 2.
      { esplits; et.
        { rr in HD1. uipropall. eapply HD1; [|refl].
          eapply wf_extends; try apply x.
          exists (ro_tgt ⋅ fr_tgt ⋅ ctx0 ⋅ mr_tgt1). r_solve.
        }
        { rr. uipropall. }
      }
      { eapply wf_extends; et. r. exists (fr_tgt ⋅ ctx0 ⋅ mr_tgt1). instantiate (1:=ε). r_solve. }
      { instantiate (1:= fr_tgt ⋅ ctx0 ⋅ mr_tgt1). r_wf x. }
      i; des. clarify.
      rr in x8. uipropall. des; ss.
      esplits; et.
      { eapply wf_extends; et. r. exists b. r_solve. }
    }
    des. (ired_both; apply sim_itreeC_spec; econs).
    exists (ro_src, fr_src ⋅ fr_tgt, mr_src1 ⋅ mr_tgt1).
    steps.
    (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    { r_wf UPDATABLE0. }
    (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    (ired_both; apply sim_itreeC_spec; econs). esplits.
    (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    ired_both. gstep. econs; eauto.
    { econs; et. i. unfold OwnT. uipropall. esplits; eauto. refl. }
    i. inv WF.

    unfold HoareCallPost at 1. unfold mget. steps.
    eapply POST; et.
    { eapply current_iPropL_push; et.
      eapply current_iPropL_push; et; cycle 1.
      { rr. uipropall. refl. }
      eapply current_iPropL_push; et; cycle 1.
      { cbn. eapply RSRC0; et. eapply wf_extends; et. exists (c ⋅ fr_src ⋅ fr_tgt ⋅ c0). r_solve. }
      eapply current_iPropL_push; et; cycle 1.
      eapply current_iPropL_nil; et.
      r_wf _ASSUME.
    }
  Unshelve. all: ss.
  Qed.

  Lemma hcall_clo_ord_weaken''
        fsp_src (x_src: shelve__ fsp_src.(meta))
        A (a0: shelve__ A) FR
        fsp_tgt


        (le: A -> A -> Prop) mn r rg _a n m mp_src0 mp_tgt0 (mr_src0 mr_tgt0: Σ)
        k_tgt k_src
        fn tbr_src tbr_tgt ord_cur_src ord_cur_tgt varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)


        ctx0 rx
        ips Xtra
        (ACC: current_iPropL ctx0 ips)
        (ENTAIL: bi_entails (from_iPropL ips) (bupd ((OwnT mr_tgt0) ** (Exactly rx Xtra))))

        (UPDATABLE: forall x_tgt,
           bi_entails (Xtra ** (fsp_tgt.(precond) (Some mn) x_tgt varg_tgt varg_tgt: iProp) **
                            ⌜ord_lt (measure fsp_tgt x_tgt) ord_cur_tgt
                             ∧ (tbr_tgt = true → is_pure (measure fsp_tgt x_tgt))
                             ∧ (tbr_tgt = false → measure fsp_tgt x_tgt = ord_top)⌝
                      )
                      (bupd (FR ** R a0 mp_src0 mp_tgt0 ** (fsp_src.(precond) (Some mn) x_src varg_src varg_tgt: iProp)
                                ** ⌜ord_lt (measure fsp_src x_src) ord_cur_src
                             ∧ (tbr_src = true → is_pure (measure fsp_src x_src))
                             ∧ (tbr_src = false → measure fsp_src x_src = ord_top)⌝)))


        (SIMPLE: forall x_tgt varg_tgt_tgt,
            (bi_entails ((precond fsp_tgt (Some mn) x_tgt varg_tgt varg_tgt_tgt): iProp) (⌜varg_tgt = varg_tgt_tgt⌝%I)))

        (POST: forall (vret_tgt : Any.t) (mr_src1 mr_tgt1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      ctx1 fr_tgt x_tgt
                      (* (ACC: current_iProp ctx1 (FR ** OwnT fr_tgt ** OwnT mr_tgt1 *)
                      (*                              ** R a1 mp_src1 mp_tgt1 ** fsp_src.(postcond) (Some mn) x_src vret_src vret_tgt)) *)
                      (ACC: current_iPropL ctx1 [("FR", FR); ("FRT", OwnT fr_tgt); ("INV", R a1 mp_src1 mp_tgt1 ** OwnT mr_tgt1);
                                                ("POST", fsp_src.(postcond) (Some mn) x_src vret_src vret_tgt)])
          ,
                gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true _a
                       (Any.pair mp_src1 mr_src1↑, k_src (ctx1, vret_src))
                       (Any.pair mp_tgt1 mr_tgt1↑, HoareCallPost mn tbr_tgt ord_cur_tgt fsp_tgt.(postcond) vret_tgt x_tgt fr_tgt >>= k_tgt)
        )
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n _a
             (Any.pair mp_src0 mr_src0↑, (HoareCall mn tbr_src ord_cur_src fsp_src fn varg_src) ctx0 >>= k_src)
             (Any.pair mp_tgt0 mr_tgt0↑, (HoareCall mn tbr_tgt ord_cur_tgt fsp_tgt fn varg_tgt) (ctx0 ⋅ rx) >>= k_tgt)
  .
  Proof.
    eapply current_iPropL_entail_all with (Hn:="A") in ACC; et.
    mDesAll.
    mAssert _ with "A1". { iAssumption. }
    mAssert _ with "A". { iAssumption. }
    eapply hcall_clo_ord_weaken'; et.
  Qed.

  Lemma hpost_clo_tgt
        A Xn Xtra Rn Frn Invtn mp_tgt mr_tgt
        mn r rg
        Invtn' Xn'
        X (Q: option mname -> X -> Any.t -> Any.t -> iProp)
        mpr_src f_src k_tgt
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        m n
        ctx x vret_tgt vret_src fr_tgt
        (ACC: current_iPropL ctx [(Rn, Q (Some mn) x vret_src vret_tgt); (Frn, OwnT fr_tgt); (Invtn, OwnT mr_tgt); (Xn, Xtra)])
        (ARG: forall
            rx
            (ACC: current_iPropL ctx [(Invtn', OwnT mr_tgt); (Xn', (Exactly rx Xtra)%I)]),
            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m true a
                   (mpr_src, f_src)
                   (Any.pair mp_tgt mr_tgt↑, k_tgt (ctx ⋅ rx, vret_src)))
        tbr ord_tgt
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (mpr_src, f_src)
             (Any.pair mp_tgt mr_tgt↑, (HoareCallPost mn tbr ord_tgt Q vret_tgt x fr_tgt >>= k_tgt))
  .
  Proof.
    (* inv WF. *)
    unfold HoareCallPost, mput, mget, assume, guarantee. steps.
    eapply current_iPropL_pop in ACC. des.
    eapply current_iPropL_pop in TL. des.
    eapply current_iPropL_pop in TL0. des.
    eapply current_iPropL_pop in TL. des. ss. clear_fast.
    eapply current_iPropL_nil in TL0. rename hdr into rret. rename hdr1 into rinv. rename hdr0 into rf. rename hdr2 into rx.
    (* apply Any.pair_inj in H2. des; clarify. apply Any.upcast_inj in H0. des; clarify. *)
    repeat (ired_both; apply sim_itreeC_spec; econs). exists (rret, (ctx ⋅ rx)).
    repeat (ired_both; apply sim_itreeC_spec; econs). esplits.
    { clear - TL0 HD1 HD0. unfold OwnT in *. uipropall. unfold URA.extends in *. des; clarify.
      eapply wf_extends; et. exists (ctx0 ⋅ ctx1). r_solve. }
    steps.
    repeat (ired_both; apply sim_itreeC_spec; econs). eexists.
    repeat (ired_both; apply sim_itreeC_spec; econs). eexists; et. steps.
    eapply ARG.
    eapply current_iPropL_push; et.
    eapply current_iPropL_push; et.
    { instantiate (1:=rx). eapply current_iPropL_nil; et.
      { eapply wf_extends; et. exists (rret ⋅ rf). r_solve. }
    }
    { rr. uipropall. splits.
      { refl. }
      { rr. uipropall. i. eapply iProp_mono; eauto. }
    }
  Unshelve. all: try exact 0.
  Qed.

  Lemma hpost_clo_tgt'
        A Xn Invtn Xtra mp_tgt mr_tgt
        mn r rg
        X (Q: option mname -> X -> Any.t -> Any.t -> iProp)
        mpr_src f_src k_tgt
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        m n
        ctx x vret_tgt vret_src fr_tgt ips
        (ACC: current_iPropL ctx ips)
        (ENTAIL: bi_entails (from_iPropL ips) (bupd (Q (Some mn) x vret_src vret_tgt ** OwnT fr_tgt ** OwnT mr_tgt ** Xtra)))
        (ARG: forall
            rx
            (ACC: current_iPropL ctx [(Invtn, OwnT mr_tgt); (Xn, (Exactly rx Xtra)%I)]),
            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m true a
                   (mpr_src, f_src)
                   (Any.pair mp_tgt mr_tgt↑, k_tgt (ctx ⋅ rx, vret_src)))
        tbr ord_tgt
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (mpr_src, f_src)
             (Any.pair mp_tgt mr_tgt↑, (HoareCallPost mn tbr ord_tgt Q vret_tgt x fr_tgt >>= k_tgt))
  .
  Proof.
    eapply current_iPropL_entail_all with (Hn:="A") in ACC; et.
    mDesAll.
    mAssert _ with "A1". { iAssumption. }
    mAssert _ with "A2". { iAssumption. }
    mAssert _ with "A3". { iAssumption. }
    mAssert _ with "A". { iAssumption. }
    eapply hpost_clo_tgt; et.
  Unshelve. all: try exact 0.
  Qed.

  Local Transparent APC.

  Definition is_possibly_pure (fsp: fspec): Prop := exists x, is_pure (fsp.(measure) x).

  Definition stb_pure_incl (stb_tgt stb_src: string -> option fspec): Prop :=
    forall fn fsp (FIND: stb_tgt fn = Some fsp) (PURE: is_possibly_pure fsp), stb_src fn = Some fsp
  .

  Local Transparent HoareCall.

  Lemma hAPC_both
        A (a0: shelve__ A) mp_src0 mp_tgt0 (mr_src0 mr_tgt0: Σ)
        mn r rg
        k_src k_tgt
        _a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        m n
        ctx0
        `{PreOrder _ le}

        (* (WF: mk_wf R a0 ((Any.pair mp_src0 mr_src0↑), (Any.pair mp_tgt0 mr_tgt0↑))) *)

        rx0
        (* ips Xtra *)
        (* (ACC: current_iPropL ctx0 ips) *)
        (* (ENTAIL: bi_entails (from_iPropL ips) ((OwnT mr_tgt0) ** (Xtra ∧ Exactly rx))) *)
        Xn Invtn Xtra
        (ACC: current_iPropL ctx0 [(Invtn, OwnT mr_tgt0); (Xn, (Exactly rx0 Xtra)%I)])
        FR
        (ENTAIL: bi_entails Xtra (R a0 mp_src0 mp_tgt0 ** FR))
        (* (WFA: forall a1 mp_src1 mp_tgt1 (mr_src1 mr_tgt1: Σ) (INV: I mr_src1), *)
        (*     mk_wf R a1 ((Any.pair mp_src1 mr_src1↑), (Any.pair mp_tgt1 mr_tgt1↑))) *)


        stb_src stb_tgt d
        (STBINCL: stb_pure_incl stb_tgt stb_src)
        (ARG: forall
            (mr_src1 mr_tgt1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
            (WLE: le a0 a1)
            ctx1 rx1
            (ACC: current_iPropL ctx1 [("INVT", OwnT mr_tgt1);
                                      ("X", (Exactly rx1 (R a1 mp_src1 mp_tgt1 ** FR))%I)]),
            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true _a
                   (Any.pair mp_src1 mr_src1↑, k_src (ctx1, tt))
                   (Any.pair mp_tgt1 mr_tgt1↑, k_tgt (ctx1 ⋅ rx1, tt)))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n _a
             (Any.pair mp_src0 mr_src0↑, (interp_hCallE_tgt mn stb_src d APC ctx0) >>= k_src)
             (Any.pair mp_tgt0 mr_tgt0↑, (interp_hCallE_tgt mn stb_tgt d APC (ctx0 ⋅ rx0)) >>= k_tgt)
  .
  Proof.
    subst.
    unfold APC. steps. force_l. exists x. steps.
    deflag.
    (* Unset Printing Notations. *)
    clear_until x. gen x d ctx0 rx0. gen mp_src0 mp_tgt0 mr_src0 mr_tgt0. gen a0. gen Xtra. gcofix CIH. i.
    {
      rewrite unfold_APC. ired_both.
      force_r. i. force_l. exists x0.
      destruct x0.
      - steps. eapply gpaco8_mon; et.
        { eapply ARG.
          { refl. }
          clear - ACC ENTAIL.
          eapply current_iPropL_pop in ACC; des.
          eapply current_iPropL_pop in TL; des.
          eapply current_iPropL_nil in TL0. ss.
          eapply current_iPropL_push; et.
          uipropall. des. clarify.
          exploit ENTAIL; try apply HD0.
          { eapply wf_extends; et. r. exists (ctx0 ⋅ hdr). instantiate (1:=hdr0).  r_solve. }
          { rr in HD1. uipropall. eapply HD1.
            { eapply wf_extends; [eapply TL0|]. exists (ctx0 ⋅ hdr). r_solve. }
            { auto. }
          }            
          i; des. clarify.
          eapply current_iPropL_push; cycle 1.
          { ss. instantiate (1:=a ⋅ b). splits; auto.
            rr. uipropall. i. eapply ENTAIL; auto.
            rr in HD1. uipropall. eapply HD1; eauto.
          }
          eapply current_iPropL_nil.
          { r_wf TL0. }
        }
      -
        assert(T: exists rf_src rm_src, R a0 mp_src0 mp_tgt0 rm_src /\ FR rf_src /\ rx0 = rf_src ⋅ rm_src).
        { clear - ACC ENTAIL. uipropall.
          eapply current_iPropL_pop in ACC. des.
          eapply current_iPropL_pop in TL. des.
          eapply current_iPropL_nil in TL0. ss.
          des. clarify.
          exploit ENTAIL; try apply HD0.
          { eapply wf_extends; et. exists (ctx0 ⋅ hdr). instantiate (1:=hdr0). r_solve. }
          { rr in HD1. uipropall. eapply HD1.
            { eapply wf_extends; [eapply TL0|]. exists (ctx0 ⋅ hdr). r_solve. }
            { auto. }
          }            
          i; des. clarify. hexploit (ENTAIL rx0).
          { eapply wf_extends; eauto. etrans ;eauto.
            exists (ctx0 ⋅ hdr). r_solve.
          }
          { rr in HD1. uipropall. eapply HD1; [|refl].
            { eapply wf_extends; eauto. etrans ;eauto.
              exists (ctx0 ⋅ hdr). r_solve.
            }
          }
          { i. des. subst. esplits; eauto. r_solve. }
        }
        des. subst.

        steps. force_l. exists x0. steps. force_l; ss. steps. unfold HoareCall. unfold mput, mget. steps.
        des; ss.
        assert(STB: stb_src s = Some f).
        { eapply STBINCL; et. r. esplits; et. }
        force_l. eexists (_, _). steps. rewrite STB. steps. instantiate (1:=t).
        unfold HoareCall. unfold mput, mget. steps.

        force_l. rename c into mr_tgt1. rename c0 into ro. rename c1 into rf.
        exists (ro, rf ⋅ rf_src, rm_src ⋅ mr_tgt1). steps. force_l; ss.
        { r_wf _GUARANTEE1. }
        steps. force_l. esplits; et. steps. force_l. esplits; et. steps. force_l. esplits; et.
        steps. force_l; et. steps. gstep. econs; eauto.
        { econs. eapply to_semantic. iIntros "[A B]". iFrame. iStopProof.
          uipropall. i. eapply iProp_mono; et.
        }

        i. inv WF. clarify. steps.
        hexploit1 RSRC.
        { eapply wf_extends; et. r. exists (c ⋅ rf ⋅ rf_src ⋅ c0). r_solve. }
        rename c into ri. rename c0 into ctx1.
        rr in RSRC. autounfold with iprop in RSRC; autorewrite with iprop in RSRC. des. clarify.
        rename a into rinv.
        force_r. exists (ri, ctx1 ⋅ (rinv ⋅ rf_src)). steps. force_r; ss.
        { rr in RSRC1. uipropall. red in RSRC1. des. subst.
          eapply wf_extends; eauto. exists ctx. r_solve.
        }
        steps. force_r. esplits. steps. force_r; et. steps.

        move CIH at bottom.
        deflag. gbase. eapply (CIH _ w1); et.
        { i. eapply ARG; try apply ACC0. etrans; et. }
        { eapply current_iPropL_push; et.
          eapply current_iPropL_push; cycle 1.
          { ss. rr. uipropall. splits.
            { refl. }
            rr. uipropall. i. r in H0. des. subst.
            exists (rinv ⋅ ctx), rf_src. esplits.
            { r_solve. }
            { eapply iProp_mono; [..|eauto]; eauto.
              { eapply wf_extends; eauto. exists rf_src. r_solve. }
              { exists ctx. r_solve. }
            }
            { eauto. }
          }
          eapply current_iPropL_nil.
          eapply wf_extends; try apply _ASSUME.
          exists (ri ⋅ rf). r_solve.
        }
    }
  Unshelve. all: try exact 0.
  Qed.

End MODE.

Global Opaque OwnT.

Ltac harg :=
  let PRE := constr:("PRE") in
  let INVS := constr:("INVS") in
  let INVT := constr:("INVT") in
  eapply (@harg_clo _ _ PRE INVS INVT);
  [eassumption
  |
  ]; i.



Ltac init :=
  let varg_src := fresh "varg_src" in
  let mn := fresh "mn" in
  let varg := fresh "varg" in
  let EQ := fresh "EQ" in
  let w := fresh "w" in
  let mrp_src := fresh "mrp_src" in
  let mp_tgt := fresh "mp_tgt" in
  let WF := fresh "WF" in
  split; rr; ss; intros varg_src [mn varg] EQ w mrp_src mp_tgt WF;
  (try subst varg_src); cbn;
  ginit;
  try (unfold fun_to_tgt, cfunN, cfunU; rewrite ! HoareFun_parse); simpl.

Ltac harg_tgt :=
  let XN := constr:("FR") in
  let INVTN := constr:("INVT") in
  eapply (@harg_clo_tgt' _ _ XN INVTN);
  [eassumption
  |start_ipm_proof
  |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H)].

Ltac hpost_tgt :=
  let XN := constr:("FR") in
  let INVTN := constr:("INVT") in
  eapply (@hpost_clo_tgt' _ _ XN INVTN);
  [eassumption
  |start_ipm_proof
  |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H)].

Tactic Notation "hcall" uconstr(x) uconstr(a) :=
  eapply (@hcall_clo_ord_weaken'' _ _ x _ a);
  unshelve_goal;
  [eassumption
  |start_ipm_proof; try (iFrame; et)
  |cbn; i; iIntros "[FR P]"
  |
  |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H)]
.

Tactic Notation "hret" uconstr(a) :=
  eapply (@hret_clo_both _ _ a); unshelve_goal;
  [eassumption
  |
  |i; iIntros "[Q FR]"
  |i; iIntros "Q"
  ].

Tactic Notation "hAPC" uconstr(a) :=
  eapply (@hAPC_both _ _ a);
  [try (typeclasses eauto)
  |eassumption
  |
  |
  |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H)]
.
