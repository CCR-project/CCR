Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef OpenDef STB SimModSem.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import ProofMode Invariant.
Require Import HTactics HSim.

Set Implicit Arguments.


Require Import Red.
Require Import IRed.

Ltac hred_l := try (prw _red_gen 1 2 1 0).
Ltac hred_r := try (prw _red_gen 1 1 1 0).
Ltac hred := try (prw _red_gen 1 1 0).


Section SIM.
  Context `{Σ: GRA.t}.
  Variable world: Type.
  Variable le: relation world.
  Variable I: world -> Any.t -> Any.t -> iProp.

  Variable mn: mname.
  Variable stb: gname -> option fspec.
  Variable o: ord.

  Let _hsim := _hsim le I mn stb o.

  Variant fn_has_spec (fn: gname) (arg_src: Any.t) (arg_tgt: Any.t)
          (pre: iProp)
          (post: Any.t -> Any.t -> iProp)
          (tbr: bool): Prop :=
  | fn_has_spec_intro
      fsp (x: fsp.(meta))
      (STB: stb fn = Some fsp)
      (MEASURE: ord_lt (fsp.(measure) x) o)
      (PRE: bi_entails pre (#=> fsp.(precond) (Some mn) x arg_src arg_tgt))
      (POST: forall ret_src ret_tgt, bi_entails (fsp.(postcond) (Some mn) x ret_src ret_tgt: iProp) (#=> post ret_src ret_tgt))
      (TBR: tbr = is_pure (fsp.(measure) x))
  .

  Lemma fn_has_spec_in_stb fsp (x: fsp.(meta))
        fn arg_src arg_tgt tbr
        (STB: stb fn = Some fsp)
        (MEASURE: ord_lt (fsp.(measure) x) o)
        (TBR: tbr = is_pure (fsp.(measure) x))
    :
      fn_has_spec
        fn arg_src arg_tgt
        (fsp.(precond) (Some mn) x arg_src arg_tgt)
        (fsp.(postcond) (Some mn) x)
        tbr.
  Proof.
    econs; eauto.
  Qed.

  Lemma fn_has_spec_impl fn arg_src arg_tgt pre0 post0 pre1 post1 tbr
        (PRE: bi_entails pre1 (#=> pre0))
        (POST: forall ret_src ret_tgt, bi_entails (post0 ret_src ret_tgt) (#=> (post1 ret_src ret_tgt)))
        (SPEC: fn_has_spec fn arg_src arg_tgt pre0 post0 tbr)
    :
      fn_has_spec fn arg_src arg_tgt pre1 post1 tbr.
  Proof.
    inv SPEC. econs; eauto.
    { iIntros "H". iPoseProof (PRE with "H") as "H".
      iMod "H". iApply PRE0. iApply "H".
    }
    { i. iIntros "H". iPoseProof (POST0 with "H") as "H".
      iMod "H". iApply POST. iApply "H".
    }
  Qed.

  Program Definition isim'
          r g f_src f_tgt
          {R_src R_tgt}
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fuel: option Ord.t)
          (st_src: Any.t * itree hEs R_src)
          (st_tgt: Any.t * itree Es R_tgt): iProp :=
    iProp_intro (fun res =>
                   forall ctx (WF: URA.wf (res ⋅ ctx)),
                     gpaco9 (_hsim) (cpn9 _hsim) r g _ _ Q ctx fuel f_src f_tgt st_src st_tgt) _.
  Next Obligation.
    i.  ss. i. eapply H. eapply URA.wf_extends; eauto. eapply URA.extends_add; eauto.
  Qed.

  Definition isim
             '(r, g, f_src, f_tgt)
             {R_src R_tgt}
             (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
             (fuel: option Ord.t)
             (st_src: Any.t * itree hEs R_src)
             (st_tgt: Any.t * itree Es R_tgt): iProp :=
    isim' r g f_src f_tgt Q fuel st_src st_tgt.

  Lemma isim_init
        R_src R_tgt (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        P r g ctx fuel f_src f_tgt st_src st_tgt itr_src itr_tgt
        (ENTAIL: bi_entails
                   P
                   (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, itr_tgt)))
        (CUR: current_iProp ctx P)
    :
      gpaco9 _hsim (cpn9 _hsim) r g _ _ Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt).
  Proof.
    eapply current_iProp_entail in ENTAIL; eauto.
    inv ENTAIL. unfold isim in IPROP. eapply IPROP; eauto.
  Qed.

  Lemma isim_final
        R_src R_tgt (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        P r g fuel f_src f_tgt st_src st_tgt itr_src itr_tgt
        (SIM: forall ctx
                     (CUR: current_iProp ctx P),
            gpaco9 _hsim (cpn9 _hsim) r g _ _ Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    :
      bi_entails
        P
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    uipropall. ii. eapply SIM. econs; eauto.
  Qed.

  Lemma isim_current
        R_src R_tgt (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ctx f_src f_tgt st_src st_tgt itr_src itr_tgt
        (CUR: current_iProp ctx (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, itr_tgt)))
    :
      gpaco9 _hsim (cpn9 _hsim) r g _ _ Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt).
  Proof.
    inv CUR. eapply IPROP; eauto.
  Qed.

  Lemma isim_upd R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt
    :
      bi_entails
        (#=> (isim (r, g, f_src, f_tgt) (fun st_src st_tgt ret_src ret_tgt => #=> Q st_src st_tgt ret_src ret_tgt) fuel st_src st_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel st_src st_tgt).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    rr in H. unfold bi_bupd_bupd in H. ss. unfold Upd in H. autorewrite with iprop in H.
    i. hexploit H; eauto. i. des.
    hexploit H1; eauto. i. guclo hmonoC_spec. econs; auto.
  Qed.

  Lemma isim_mono R_src R_tgt
        (Q0 Q1: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src itr_src st_tgt itr_tgt
        (MONO: forall st_src st_tgt ret_src ret_tgt,
            (bi_entails (Q0 st_src st_tgt ret_src ret_tgt) (Q1 st_src st_tgt ret_src ret_tgt)))
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) Q0 fuel (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q1 fuel (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i. hexploit H; eauto. i.
    guclo hmonoC_spec. econs; eauto. i. iIntros "H".
    iModIntro. iApply MONO. auto.
  Qed.

  Lemma isim_wand R_src R_tgt
        (Q0 Q1: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src itr_src st_tgt itr_tgt
    :
      bi_entails
        ((∀ st_src st_tgt ret_src ret_tgt,
             ((Q0 st_src st_tgt ret_src ret_tgt) -∗ (Q1 st_src st_tgt ret_src ret_tgt))) ** (isim (r, g, f_src, f_tgt) Q0 fuel (st_src, itr_src) (st_tgt, itr_tgt)))
        (isim (r, g, f_src, f_tgt) Q1 fuel (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' in *. rr. i.
    rr in H. unfold Sepconj in H. autorewrite with iprop in H.
    des. clarify. eapply from_semantic in H0. hexploit (H1 (ctx ⋅ a)).
    { r_wf WF0. }
    i. guclo hframeC_aux_spec. econs.
    { instantiate (1:=a). eapply URA.wf_mon. instantiate (1:=b). r_wf WF0. }
    guclo hmonoC_spec. econs.
    { eapply H. }
    i. iIntros "H0". iModIntro. iIntros "H1".
    iPoseProof (H0 with "H1") as "H1".
    iMod "H1". iApply "H1". iApply "H0".
  Qed.

  Lemma isim_bind R_src R_tgt S_src S_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src (itr_src: itree hEs S_src)
        ktr_src st_tgt (itr_tgt: itree Es S_tgt) ktr_tgt
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) (fun st_src st_tgt ret_src ret_tgt => isim (r, g, false, false) Q None (st_src, ktr_src ret_src) (st_tgt, ktr_tgt ret_tgt)) fuel (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src >>= ktr_src) (st_tgt, itr_tgt >>= ktr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    guclo hbindC_spec. econs.
    { eapply H; eauto. }
    i. inv POST. eapply IPROP. eauto.
  Qed.

  Lemma isim_bind_left R_src R_tgt S_src
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src (itr_src: itree hEs S_src)
        ktr_src st_tgt itr_tgt
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) (fun st_src st_tgt ret_src ret_tgt => isim (r, g, false, false) Q None (st_src, ktr_src ret_src) (st_tgt, itr_tgt)) fuel (st_src, itr_src) (st_tgt, Ret tt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    iIntros "H".
    assert (EQ: itr_tgt = Ret tt >>= fun _ => itr_tgt).
    { grind. }
    rewrite EQ. iApply isim_bind. rewrite <- EQ. iApply "H".
  Qed.

  Lemma isim_bind_right R_src R_tgt S_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src itr_src
        st_tgt (itr_tgt: itree Es S_tgt) ktr_tgt
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) (fun st_src st_tgt ret_src ret_tgt => isim (r, g, false, false) Q None (st_src, itr_src) (st_tgt, ktr_tgt ret_tgt)) fuel (st_src, Ret tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, itr_tgt >>= ktr_tgt)).
  Proof.
    iIntros "H".
    assert (EQ: itr_src = Ret tt >>= fun _ => itr_src).
    { grind. }
    rewrite EQ. iApply isim_bind. rewrite <- EQ. iApply "H".
  Qed.

  Lemma isim_bind_right_pure R_src R_tgt S_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src itr_src
        st_tgt (itr_tgt: itree Es S_tgt) ktr_tgt
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) (fun st_src st_tgt ret_src ret_tgt => isim (r, g, false, false) Q fuel (st_src, itr_src) (st_tgt, ktr_tgt ret_tgt)) None (st_src, Ret tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, itr_tgt >>= ktr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    guclo hbind_rightC_spec. econs.
    { eapply H; eauto. }
    i. inv POST. eapply IPROP. eauto.
  Qed.

  Lemma isim_split_aux R_src R_tgt S_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g st_src itr_src st_tgt (itr_tgt: itree Es S_tgt) ktr_tgt
        fuel0 fuel1 f_src f_tgt
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) (fun st_src st_tgt _ ret_tgt => isim (r, g, false, false) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt ret_tgt)) (Some fuel0) (st_src, Ret tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q (Some (fuel1 + fuel0)%ord) (st_src, itr_src) (st_tgt, itr_tgt >>= ktr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    guclo hsplitC_spec. econs.
    { eapply H; eauto. }
    i. inv POST. eapply IPROP. eauto.
  Qed.

  Lemma isim_call_impure
        pre post w0
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt fn arg_src arg_tgt ktr_src ktr_tgt
        (SPEC: fn_has_spec fn arg_src arg_tgt pre post false)
    :
      bi_entails
        ((inv_with le I w0 st_src st_tgt)
           ** (pre: iProp)
           ** (∀ st_src st_tgt ret_src ret_tgt,
                  inv_with le I w0 st_src st_tgt -* (post ret_src ret_tgt: iProp) -* isim (g, g, true, true) Q None (st_src, ktr_src ret_src) (st_tgt, ktr_tgt ret_tgt)))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, trigger (Call fn arg_src) >>= ktr_src) (st_tgt, trigger (Call fn arg_tgt) >>= ktr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' at 2. rr. i.
    match (type of H) with
    | (iProp_pred ?P) _ =>
      assert (CUR: current_iProp ctx P)
    end.
    { econs; eauto. }
    apply current_iPropL_convert in CUR. mDesAll.
    ired_both. gstep. inv SPEC. econs; eauto.
    { mAssert _ with "A1".
      { iApply (PRE with "A1"). }
      mUpd "A2".
      eapply current_iProp_entail; [eapply CUR|]. start_ipm_proof.
      iSplitR "A2"; [|iExact "A2"].
      iSplitR "H"; [|iExact "H"].
      iExact "A".
    }
    { revert MEASURE TBR. generalize o. i. destruct (measure fsp x), o0; ss. }
    { revert MEASURE TBR. generalize o. i. destruct (measure fsp x), o0; ss. }
    i. apply current_iPropL_convert in ACC.
    mDesAll. mSpcUniv "H" with st_src1.
    mSpcUniv "H" with st_tgt1.
    mSpcUniv "H" with ret_src.
    mSpcUniv "H" with ret_tgt.
    mAssert _ with "A".
    { iApply (POST with "A"). }
    mUpd "A2".
    mAssert (isim (g, g, true, true) Q None (st_src1, ktr_src ret_src)
                  (st_tgt1, ktr_tgt ret_tgt)) with "*".
    { iApply ("H" with "A1 A2"). }
    inv ACC. rr in IPROP. uipropall. des. subst.
    eapply IPROP0. eapply URA.wf_mon. instantiate (1:=b). r_wf GWF.
  Qed.

  Lemma isim_call_pure
        pre post w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt fn arg_src arg_tgt itr_src ktr_tgt
        fuel0
        (SPEC: fn_has_spec fn arg_src arg_tgt pre post true)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (pre: iProp)
                  **
                  (∀ st_src st_tgt ret_src ret_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (post ret_src ret_tgt: iProp)) -* isim (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt ret_tgt)))
        (isim (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, trigger (Call fn arg_tgt) >>= ktr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' at 2. rr. i.
    match (type of H) with
    | (iProp_pred ?P) _ =>
      assert (CUR: current_iProp ctx P)
    end.
    { econs; eauto. }
    apply current_iPropL_convert in CUR.
    mDesAll. ired_both. gstep. inv SPEC. econs; eauto.
    { mAssert _ with "A1".
      { iApply (PRE with "A1"). }
      mUpd "A2".
      eapply current_iProp_entail; [eapply CUR|]. start_ipm_proof.
      iSplitR "A2"; [|iExact "A2"].
      iSplitR "H"; [|iExact "H"].
      iExact "A".
    }
    { revert MEASURE TBR. generalize o. i. destruct (measure fsp x), o0; ss. }
    esplits; eauto.
    i. apply current_iPropL_convert in ACC.
    mDesAll. mSpcUniv "H" with st_src1.
    mSpcUniv "H" with st_tgt1.
    mSpcUniv "H" with ret_src.
    mSpcUniv "H" with ret_tgt.
    mAssert _ with "A".
    { iApply (POST with "A"). }
    mUpd "A2".
    mAssert (isim (g, g, true, true) Q (Some fuel1) (st_src1, itr_src) (st_tgt1, ktr_tgt ret_tgt)) with "*".
    { iApply "H". iSplitR "A2"; auto. }
    inv ACC. rr in IPROP. uipropall. des. subst. eapply IPROP0.
    eapply URA.wf_mon. instantiate (1:=b). r_wf GWF.
  Qed.

  Lemma isim_apc
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt ktr_src itr_tgt
        fuel0
    :
      bi_entails
        (∃ fuel1, isim (r, g, true, f_tgt) Q fuel1 (st_src, ktr_src tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel0 (st_src, trigger hAPC >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i.
    inv CUR. rr in IPROP. uipropall. des.
    eapply hsimC_uclo. econs; eauto.
  Qed.

  Lemma isim_progress R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel st_src itr_src st_tgt itr_tgt
    :
      bi_entails
        (isim (g, g, false, false) Q fuel (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, true, true) Q fuel (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply isim_current in CUR.
    eapply hsim_progress_flag. auto.
  Qed.

  Lemma isim_knowledge_mon
        r0 g0
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r1 g1 st_src itr_src st_tgt itr_tgt
        fuel f_src f_tgt
        (LE0: r0 <9= r1)
        (LE1: g0 <9= g1)
    :
      bi_entails
        (isim (r0, g0, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r1, g1, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply isim_current in CUR.
    eapply gpaco9_mon; eauto.
  Qed.

  Lemma isim_flag_mon
        fuel0 f_src0 f_tgt0
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g st_src itr_src st_tgt itr_tgt
        fuel1 f_src1 f_tgt1
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
        (FUEL: option_Ord_le fuel0 fuel1)
    :
      bi_entails
        (isim (r, g, f_src0, f_tgt0) Q fuel0 (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src1, f_tgt1) Q fuel1 (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply isim_current in CUR.
    guclo hflagC_spec. econs; eauto.
  Qed.

  Lemma isim_split
        fuel0 fuel1
        R_src R_tgt S_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g st_src itr_src st_tgt (itr_tgt: itree Es S_tgt) ktr_tgt
        fuel f_src f_tgt
        (FUEL: (fuel1 + fuel0 <= fuel)%ord)
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) (fun st_src st_tgt _ ret_tgt => isim (r, g, false, false) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt ret_tgt)) (Some fuel0) (st_src, Ret tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q (Some fuel) (st_src, itr_src) (st_tgt, itr_tgt >>= ktr_tgt)).
  Proof.
    iIntros "H".
    iApply isim_flag_mon.
    { eauto. }
    { eauto. }
    { instantiate (1:=Some (fuel1 + fuel0)%ord). ss. }
    iApply isim_split_aux. auto.
  Qed.

  Lemma isim_ret
        R_src R_tgt (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g
        v_src v_tgt
        st_src st_tgt
        fuel f_src f_tgt
    :
      bi_entails
        (Q st_src st_tgt v_src v_tgt)
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, Ret v_src) (st_tgt, (Ret v_tgt))).
  Proof.
    eapply isim_final. i.
    eapply hsimC_uclo. econs; eauto.
  Qed.

  Lemma isim_apc_trigger
        R_tgt
        (Q: Any.t -> Any.t -> unit -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt itr_tgt
        fuel0
    :
      bi_entails
        (∃ fuel1, isim (r, g, true, f_tgt) Q fuel1 (st_src, Ret tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel0 (st_src, trigger hAPC) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (hAPC))).
    iIntros "H". iApply isim_apc. iExact "H".
  Qed.

  Lemma isim_call_impure_trigger
        pre post w0
        (Q: Any.t -> Any.t -> Any.t -> Any.t -> iProp)
        r g fuel f_src f_tgt st_src st_tgt fn arg_src arg_tgt
        (SPEC: fn_has_spec fn arg_src arg_tgt pre post false)
    :
      bi_entails
        ((inv_with le I w0 st_src st_tgt)
           ** (pre: iProp)
           **
           (∀ st_src st_tgt ret_src ret_tgt,
               (inv_with le I w0 st_src st_tgt) -* (post ret_src ret_tgt: iProp) -* Q st_src st_tgt ret_src ret_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, trigger (Call fn arg_src)) (st_tgt, trigger (Call fn arg_tgt))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Call fn arg_src))).
    erewrite (@idK_spec _ _ (trigger (Call fn arg_tgt))).
    iIntros "H". iApply isim_call_impure; eauto.
    iDestruct "H" as "[H0 H1]". iSplitL "H0"; auto.
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0 H2".
    iApply isim_ret. iApply ("H1" with "H0 H2").
  Qed.

  Lemma isim_call_pure_trigger
        pre post w0
        (Q: Any.t -> Any.t -> unit -> Any.t -> iProp)
        r g f_src f_tgt st_src st_tgt fn arg_src arg_tgt
        (SPEC: fn_has_spec fn arg_src arg_tgt pre post true)
    :
      bi_entails
        ((inv_with le I w0 st_src st_tgt)
           ** (pre: iProp)
           **
           (∀ st_src st_tgt ret_src ret_tgt,
               (inv_with le I w0 st_src st_tgt) -* (post ret_src ret_tgt: iProp) -* Q st_src st_tgt tt ret_tgt))
        (isim (r, g, f_src, f_tgt) Q (Some (1: Ord.t)) (st_src, Ret tt) (st_tgt, trigger (Call fn arg_tgt))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Call fn arg_tgt))).
    iIntros "H". iApply isim_call_pure; eauto.
    { oauto. }
    iDestruct "H" as "[H0 H1]". iSplitL "H0"; auto.
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "[H0 H2]".
    iApply isim_ret. iApply ("H1" with "H0 H2").
  Qed.

  Global Instance iProp_isim_absorbing
         R_src R_tgt r g (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
         fuel f_src f_tgt st_src st_tgt:
    Absorbing (isim (r, g, f_src, f_tgt) Q fuel st_src st_tgt).
  Proof.
    unfold Absorbing. unfold bi_absorbingly.
    iIntros "[H0 H1]". iApply isim_upd.
    iDestruct "H0" as "%". iModIntro.
    destruct st_src, st_tgt. iApply isim_mono; [|iApply "H1"].
    i. ss. iIntros "H". iModIntro. auto.
  Qed.

  Global Instance iProp_isim_elim_upd
         R_src R_tgt r g (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
         fuel f_src f_tgt st_src st_tgt
         P:
    ElimModal True false false (#=> P) P (isim (r, g, f_src, f_tgt) Q fuel st_src st_tgt) (isim (r, g, f_src, f_tgt) Q fuel st_src st_tgt).
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    destruct st_src, st_tgt. iApply isim_mono; [|iApply "H1"; auto].
    i. ss. iIntros "H". iModIntro. auto.
  Qed.

  Lemma isim_syscall
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        fn arg rvs
        r g fuel f_src f_tgt st_src st_tgt ktr_src ktr_tgt
    :
      bi_entails
        (∀ ret, isim (g, g, true, true) Q None (st_src, ktr_src ret) (st_tgt, ktr_tgt ret))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    i. inv CUR. rr in IPROP. uipropall. eapply IPROP; eauto.
  Qed.

  Lemma isim_syscall_trigger
        (Q: Any.t -> Any.t -> Any.t -> Any.t -> iProp)
        fn arg_src arg_tgt rvs
        r g fuel f_src f_tgt st_src st_tgt
    :
      bi_entails
        (⌜arg_src = arg_tgt⌝ ** ∀ ret, Q st_src st_tgt ret ret)
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, trigger (Syscall fn arg_src rvs)) (st_tgt, trigger (Syscall fn arg_tgt rvs))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Syscall fn arg_src rvs))).
    erewrite (@idK_spec _ _ (trigger (Syscall fn arg_tgt rvs))).
    iIntros "[% H1]". subst.
    iApply isim_syscall. iIntros (ret).
    iApply isim_ret. iApply "H1".
  Qed.

  Lemma isim_tau_src
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt itr_src itr_tgt
    :
      bi_entails
        (isim (r, g, true, f_tgt) Q None (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, tau;; itr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_tau_tgt
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt itr_src itr_tgt
    :
      bi_entails
        (isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, tau;; itr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_choose_src
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt X ktr_src itr_tgt
    :
      bi_entails
        (∃ x, isim (r, g, true, f_tgt) Q None (st_src, ktr_src x) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    inv CUR. rr in IPROP. uipropall. des. esplits. eapply IPROP; eauto.
  Qed.

  Lemma isim_choose_src_trigger
        X R_tgt
        (Q: Any.t -> Any.t -> X -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt itr_tgt
    :
      bi_entails
        (∃ x, isim (r, g, true, f_tgt) Q None (st_src, Ret x) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, trigger (Choose X)) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Choose X))).
    iIntros "H". iApply isim_choose_src.
    iDestruct "H" as (x) "H". iExists x. auto.
  Qed.

  Lemma isim_choose_tgt
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt X itr_src ktr_tgt
    :
      bi_entails
        (∀ x, isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt, ktr_tgt x))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    inv CUR. rr in IPROP. uipropall. i. eapply IPROP; eauto.
  Qed.

  Lemma isim_choose_tgt_trigger
        R_src X
        (Q: Any.t -> Any.t -> R_src -> X -> iProp)
        r g fuel f_src f_tgt st_src st_tgt itr_src
    :
      bi_entails
        (∀ x, isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt, Ret x))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, trigger (Choose X))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Choose X))).
    iIntros "H". iApply isim_choose_tgt.
    iIntros (x). iApply "H".
  Qed.

  Lemma isim_take_src
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt X ktr_src itr_tgt
    :
      bi_entails
        (∀ x, isim (r, g, true, f_tgt) Q None (st_src, ktr_src x) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    inv CUR. rr in IPROP. uipropall. i. eapply IPROP; eauto.
  Qed.

  Lemma isim_take_src_trigger
        X R_tgt
        (Q: Any.t -> Any.t -> X -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt itr_tgt
    :
      bi_entails
        (∀ x, isim (r, g, true, f_tgt) Q None (st_src, Ret x) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, trigger (Take X)) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Take X))).
    iIntros "H". iApply isim_take_src.
    iIntros (x). iApply "H".
  Qed.

  Lemma isim_take_tgt
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt X itr_src ktr_tgt
    :
      bi_entails
        (∃ x, isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt, ktr_tgt x))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    inv CUR. rr in IPROP. uipropall. des. esplits. eapply IPROP; eauto.
  Qed.

  Lemma isim_take_tgt_trigger
        R_src X
        (Q: Any.t -> Any.t -> R_src -> X -> iProp)
        r g fuel f_src f_tgt st_src st_tgt itr_src
    :
      bi_entails
        (∃ x, isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt, Ret x))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, trigger (Take X))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Take X))).
    iIntros "H". iApply isim_take_tgt.
    iDestruct "H" as (x) "H". iExists x. iApply "H".
  Qed.

  Lemma isim_pput_src
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src0 st_src1 st_tgt ktr_src itr_tgt
    :
      bi_entails
        (isim (r, g, true, f_tgt) Q None (st_src1, ktr_src tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_pput_src_trigger
        R_tgt
        (Q: Any.t -> Any.t -> unit -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src0 st_src1 st_tgt itr_tgt
    :
      bi_entails
        (isim (r, g, true, f_tgt) Q None (st_src1, Ret tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src0, trigger (PPut st_src1)) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (PPut st_src1))).
    iIntros "H". iApply isim_pput_src. iApply "H".
  Qed.

  Lemma isim_pget_src
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt ktr_src itr_tgt
    :
      bi_entails
        (isim (r, g, true, f_tgt) Q None (st_src, ktr_src st_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_get_src_trigger
        R_tgt
        (Q: Any.t -> Any.t -> Any.t -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt itr_tgt
    :
      bi_entails
        (isim (r, g, true, f_tgt) Q None (st_src, Ret st_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, trigger (PGet)) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (PGet))).
    iIntros "H". iApply isim_pget_src. iApply "H".
  Qed.

  Lemma isim_pput_tgt
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt0 st_tgt1 itr_src ktr_tgt
    :
      bi_entails
        (isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt1, ktr_tgt tt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_pput_tgt_trigger
        R_src
        (Q: Any.t -> Any.t -> R_src -> unit -> iProp)
        r g fuel f_src f_tgt st_src st_tgt0 st_tgt1 itr_src
    :
      bi_entails
        (isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt1, Ret tt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (PPut st_tgt1))).
    iIntros "H". iApply isim_pput_tgt. iApply "H".
  Qed.

  Lemma isim_pget_tgt
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt itr_src ktr_tgt
    :
      bi_entails
        (isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_pget_tgt_trigger
        R_src
        (Q: Any.t -> Any.t -> R_src -> Any.t -> iProp)
        r g fuel f_src f_tgt st_src st_tgt itr_src
    :
      bi_entails
        (isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt, Ret st_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, trigger (PGet))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (PGet))).
    iIntros "H". iApply isim_pget_tgt. iApply "H".
  Qed.

  Lemma isim_assume_src
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt P k_src i_tgt
    :
      bi_entails
        (⌜P⌝ -* isim (r, g, true, f_tgt) Q None (st_src, k_src tt) (st_tgt, i_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, assume P >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". unfold assume. hred_l.
    iApply isim_take_src. iIntros (H). hred_l. iApply "H". iPureIntro. auto.
  Qed.

  Lemma isim_assume_src_trigger
        R_tgt
        (Q: Any.t -> Any.t -> unit -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt P itr_tgt
    :
      bi_entails
        (⌜P⌝ -* isim (r, g, true, f_tgt) Q None (st_src, Ret tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, assume P) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (assume P)).
    iIntros "H". iApply isim_assume_src.
    iIntros "H0". iApply "H". auto.
  Qed.

  Lemma isim_assume_tgt
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt P itr_src ktr_tgt
    :
      bi_entails
        (⌜P⌝ ∧ isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt, ktr_tgt tt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, assume P >>= ktr_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as "[% H]".
    unfold assume. hred_r. iApply isim_take_tgt.
    iExists H. hred_r. iApply "H".
  Qed.

  Global Instance iProp_pure_elim_affine
         P (Q: iProp):
    ElimModal True false false (<affine> ⌜P⌝) (⌜P⌝) Q Q.
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iApply "H1". iApply "H0".
  Qed.

  Lemma isim_assume_tgt_trigger
        R_src
        (Q: Any.t -> Any.t -> R_src -> unit -> iProp)
        r g fuel f_src f_tgt st_src st_tgt P itr_src
    :
      bi_entails
        (⌜P⌝ ∧ isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt, Ret tt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, assume P)).
  Proof.
    erewrite (@idK_spec _ _ (assume P)).
    iIntros "H". iApply isim_assume_tgt. iSplit; auto.
    { iDestruct "H" as "[H _]". iApply "H". }
    { iDestruct "H" as "[_ H]". iApply "H". }
  Qed.

  Lemma isim_guarantee_src
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt P ktr_src itr_tgt
    :
      bi_entails
        (⌜P⌝ ∧ isim (r, g, true, f_tgt) Q None (st_src, ktr_src tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, guarantee P >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as "[% H]".
    unfold guarantee. hred_l. iApply isim_choose_src.
    iExists H. hred_l. iApply "H".
  Qed.

  Lemma isim_guarantee_src_trigger
        R_tgt
        (Q: Any.t -> Any.t -> unit -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt P itr_tgt
    :
      bi_entails
        (⌜P⌝ ∧ isim (r, g, true, f_tgt) Q None (st_src, Ret tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, guarantee P) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (guarantee P)).
    iIntros "H". iApply isim_guarantee_src. iSplit; auto.
    { iDestruct "H" as "[H _]". iApply "H". }
    { iDestruct "H" as "[_ H]". iApply "H". }
  Qed.

  Lemma isim_guarantee_tgt
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt P itr_src ktr_tgt
    :
      bi_entails
        (⌜P⌝ -* isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt, ktr_tgt tt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, guarantee P >>= ktr_tgt)).
  Proof.
    iIntros "H". unfold guarantee. hred_r.
    iApply isim_choose_tgt.
    iIntros (H). hred_r. iApply "H". iPureIntro. auto.
  Qed.

  Lemma isim_guarantee_tgt_trigger
        R_src
        (Q: Any.t -> Any.t -> R_src -> unit -> iProp)
        r g fuel f_src f_tgt st_src st_tgt P itr_src
    :
      bi_entails
        (⌜P⌝ -* isim (r, g, f_src, true) Q fuel (st_src, itr_src) (st_tgt, Ret tt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, guarantee P)).
  Proof.
    erewrite (@idK_spec _ _ (guarantee P)).
    iIntros "H". iApply isim_guarantee_tgt.
    iIntros "H0". iApply "H". auto.
  Qed.

  Lemma isim_triggerUB_src
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt X (ktr_src: X -> _) itr_tgt
    :
      bi_entails
        (⌜True⌝)
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, triggerUB >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    iIntros "H". unfold triggerUB. hred_l. iApply isim_take_src.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerUB_src_trigger
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt itr_tgt
    :
      bi_entails
        (⌜True⌝)
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, triggerUB) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (triggerUB)).
    iIntros "H". iApply isim_triggerUB_src. auto.
  Qed.

  Lemma isim_triggerNB_tgt
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt X itr_src (ktr_tgt: X -> _)
    :
      bi_entails
        (⌜True⌝)
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, triggerNB >>= ktr_tgt)).
  Proof.
    iIntros "H". unfold triggerNB. hred_r. iApply isim_choose_tgt.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerNB_trigger
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt itr_src
    :
      bi_entails
        (⌜True⌝)
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, triggerNB)).
  Proof.
    erewrite (@idK_spec _ _ (triggerNB)).
    iIntros "H". iApply isim_triggerNB_tgt. auto.
  Qed.

  Lemma isim_unwrapU_src
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt X (x: option X) ktr_src itr_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, f_src, f_tgt) Q fuel (st_src, ktr_src x') (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, unwrapU x >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    iIntros "H". unfold unwrapU. destruct x.
    { hred_l. iApply "H". auto. }
    { iApply isim_triggerUB_src. auto. }
  Qed.

  Lemma isim_unwrapU_src_trigger
        X R_tgt
        (Q: Any.t -> Any.t -> X -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt x itr_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, f_src, f_tgt) Q fuel (st_src, Ret x') (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, unwrapU x) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapU x)).
    iIntros "H". iApply isim_unwrapU_src.
    iIntros (x') "EQ". iApply "H"; auto.
  Qed.

  Lemma isim_unwrapN_src
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt X (x: option X) ktr_src itr_tgt
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, f_src, f_tgt) Q fuel (st_src, ktr_src x') (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, unwrapN x >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]".
    subst. hred_l. iApply "H".
  Qed.

  Lemma isim_unwrapN_src_trigger
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt x itr_tgt
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, f_src, f_tgt) Q fuel (st_src, Ret x') (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, unwrapN x) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapN x)).
    iIntros "H". iDestruct "H" as (x') "[% H]".
    iApply isim_unwrapN_src. iExists x'. iSplit; auto.
  Qed.

  Lemma isim_unwrapU_tgt
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt X (x: option X) itr_src ktr_tgt
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, ktr_tgt x'))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, unwrapU x >>= ktr_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst.
    hred_r. iApply "H".
  Qed.

  Lemma isim_unwrapU_tgt_trigger
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt x itr_src
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, Ret x'))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, unwrapU x)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapU x)).
    iIntros "H". iDestruct "H" as (x') "[% H]".
    iApply isim_unwrapU_tgt. iExists x'. iSplit; auto.
  Qed.

  Lemma isim_unwrapN_tgt
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt X (x: option X) itr_src ktr_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, ktr_tgt x'))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, unwrapN x >>= ktr_tgt)).
  Proof.
    iIntros "H". unfold unwrapN. destruct x.
    { hred_r. iApply "H". auto. }
    { iApply isim_triggerNB_tgt. auto. }
  Qed.

  Lemma isim_unwrapN_tgt_trigger
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt x itr_src
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, Ret x'))
        (isim (r, g, f_src, f_tgt) Q fuel (st_src, itr_src) (st_tgt, unwrapN x)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapN x)).
    iIntros "H". iApply isim_unwrapN_tgt.
    iIntros (x') "EQ". iApply "H"; auto.
  Qed.

  Lemma isim_ccallU_pure
        pre post w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        fn X Y arg_src (arg_tgt: X) itr_src (ktr_tgt: Y -> _)
        fuel0
        (SPEC: fn_has_spec fn arg_src (Any.upcast arg_tgt) pre post true)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (pre: iProp)
                  **
                  (∀ st_src st_tgt ret_src ret_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (post ret_src ret_tgt: iProp)) -* ∃ ret_tgt', ⌜ret_tgt = Any.upcast ret_tgt'⌝ ∧ isim (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt ret_tgt')))
        (isim (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU fn arg_tgt >>= ktr_tgt)).
  Proof.
    iIntros "[H0 H1]". unfold ccallU. hred_r. iApply isim_call_pure; eauto.
    iSplitL "H0"; [iExact "H0"|].
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iPoseProof ("H1" with "H0") as (ret_tgt') "[% H1]". subst.
    hred_r. iApply "H1".
  Qed.
End SIM.

Global Opaque isim.

Section TRIVIAL.
  Context `{Σ: GRA.t}.

  Definition world_trivial: Type := unit.
  Definition world_le_trivial: relation world_trivial := top2.
  Definition world_wf_trivial: world_trivial -> Any.t -> Any.t -> iProp :=
    fun _ st_src st_tgt =>
      (⌜st_src = Any.upcast tt /\ st_tgt = Any.upcast tt⌝)%I
  .

  Global Program Instance world_le_trivial_PreOrder: PreOrder world_le_trivial.

  Lemma world_wf_trivial_unit
        w r
    :
      mk_wf
        world_wf_trivial
        w
        (Any.pair (Any.upcast tt) (Any.upcast (r: Σ)), Any.upcast tt).
  Proof.
    econs. eapply to_semantic.
    iIntros "H". unfold world_wf_trivial. auto.
  Qed.

  Lemma world_wf_trivial_init
    :
      exists w_init,
        mk_wf
          world_wf_trivial
          w_init
          (Any.pair (Any.upcast tt) (Any.upcast (ε: Σ)), Any.upcast tt).
  Proof.
    exists tt. eapply world_wf_trivial_unit.
  Qed.

  Lemma world_wf_trivial_inv_with
        w
    :
      (⊢
         inv_with
         world_le_trivial
         world_wf_trivial
         w
         (Any.upcast tt)
         (Any.upcast tt)).
  Proof.
    iStartProof. iApply inv_with_current.
    unfold world_wf_trivial. auto.
  Qed.

  Variable mn: mname.
  Variable stb: gname -> option fspec.
  Variable o: ord.

  Definition isim_trivial {R} (Q: R -> iProp) (p: itree Es R): iProp :=
    (∃ fuel,
        isim
          world_le_trivial world_wf_trivial mn stb o
          (bot9, bot9, false, false)
          (fun st_src st_tgt ret_src ret_tgt =>
             (Q ret_tgt ** ⌜st_src = Any.upcast tt /\ st_tgt = Any.upcast tt⌝))
          (Some fuel)
          (Any.upcast tt, Ret tt)
          (Any.upcast tt, p))%I
  .

  Lemma isim_trivial_init
        w r g f_src f_tgt R Q fuel st_src st_tgt (itr: itree Es R)
    :
      bi_entails
        ((inv_with world_le_trivial world_wf_trivial w st_src st_tgt)
           **
           isim_trivial (fun ret => Q (Any.upcast tt) (Any.upcast tt) tt ret) itr)
        (isim
           world_le_trivial world_wf_trivial mn stb o
           (r, g, f_src, f_tgt)
           Q
           fuel
           (st_src, trigger hAPC)
           (st_tgt, itr)).
  Proof.
    unfold isim_trivial. iIntros "[H0 H1]".
    iDestruct "H1" as (fuel0) "H1". iApply isim_apc_trigger.
    iExists (Some fuel0).
    iEval (unfold inv_with, world_wf_trivial) in "H0".
    iDestruct "H0" as (w1) "[% _]". des. subst.
    iApply isim_knowledge_mon.
    { instantiate (1:=bot9). ss. }
    { instantiate (1:=bot9). ss. }
    iApply isim_upd. iModIntro.
    iApply isim_mono.
    2:{ iApply isim_flag_mon; [..|iApply "H1"]; ss. refl. }
    i. ss. iIntros "[H0 %]". des; subst.
    iModIntro. destruct ret_src. auto.
  Qed.

  Lemma isim_trivial_final
        R Q fuel (itr: itree Es R)
    :
      bi_entails
        (isim
           world_le_trivial world_wf_trivial mn stb o
           (bot9, bot9, false, false)
           (fun st_src st_tgt ret_src ret_tgt =>
              (Q ret_tgt ** ⌜st_src = Any.upcast tt /\ st_tgt = Any.upcast tt⌝))
           (Some fuel)
           (Any.upcast tt, Ret tt)
           (Any.upcast tt, itr))
        (isim_trivial Q itr).
  Proof.
    unfold isim_trivial. iIntros "H". iExists fuel. auto.
  Qed.

  Lemma isim_trivial_mono R
        (Q0 Q1: R -> iProp)
        itr
        (MONO: forall ret,
            (bi_entails (Q0 ret) (Q1 ret)))
    :
      bi_entails
        (isim_trivial Q0 itr)
        (isim_trivial Q1 itr).
  Proof.
    unfold isim_trivial. iIntros "H".
    iDestruct "H" as (fuel) "SIM". iExists fuel.
    iApply isim_mono; [|iExact "SIM"].
    iIntros (? ? ? ?) "[POST EQ]".
    iPoseProof (MONO with "POST") as "POST". iFrame.
  Qed.

  Lemma isim_trivial_wand R
        (Q0 Q1: R -> iProp)
        itr
    :
      bi_entails
        ((∀ ret,
             ((Q0 ret) -∗ (Q1 ret))) ** (isim_trivial Q0 itr))
        (isim_trivial Q1 itr).
  Proof.
    unfold isim_trivial. iIntros "[MONO H]".
    iDestruct "H" as (fuel) "SIM". iExists fuel.
    iApply isim_wand. iSplitR "SIM"; [|iExact "SIM"].
    iIntros (? ? ? ?) "[POST EQ]".
    iSpecialize ("MONO" with "POST"). iFrame.
  Qed.

  Lemma isim_trivial_init_pure
        w r g f_src f_tgt Q fuel st_src st_tgt (itr: itree Es Any.t)
    :
      bi_entails
        ((inv_with world_le_trivial world_wf_trivial w st_src st_tgt)
           **
           isim_trivial (fun ret => Q (Any.upcast tt) (Any.upcast tt) ret ret) itr)
        (isim
           world_le_trivial world_wf_trivial mn stb o
           (r, g, f_src, f_tgt)
           Q
           fuel
           (st_src, trigger hAPC >>= (fun _ => trigger (Choose Any.t)))
           (st_tgt, itr)).
  Proof.
    assert (itr = itr >>= idK).
    { grind. }
    iIntros "[H0 H1]". iEval (rewrite H). iApply isim_bind.
    iApply isim_trivial_init. iFrame.
    ss. iApply isim_trivial_mono.
    2:{ iApply "H1". }
    i. ss. iIntros "H". iApply isim_choose_src_trigger.
    iExists _. iApply isim_ret. eauto.
  Qed.

  From Ordinal Require Import ClassicalOrdinal.
  Lemma ord_exist X (P: X -> Ord.t -> Prop)
    :
      exists o_top,
      forall x (EXIST: exists o, P x o),
        (exists o, P x o /\ Ord.le o o_top).
  Proof.
    hexploit (ClassicalChoice.choice (fun x o1 => forall o0, P x o0 -> P x o1)).
    { i. destruct (classic (exists o1, P x o1)).
      { des. exists o1. eauto. }
      { exists Ord.O. i. exfalso. eauto. }
    }
    i. des. exists (Ord.join f). i. des.
    eapply H in EXIST. esplits; eauto.
    eapply Ord.join_upperbound.
  Qed.

  Lemma ord_exist_iProp (P: Ord.t -> iProp)
    :
      exists o_top,
        (bi_entails
           (∃ (o: Ord.t), P o)
           (∃ (o: Ord.t), P o ∧ ⌜Ord.le o o_top⌝)).
  Proof.
    hexploit (ord_exist (fun (r: Σ) (o0: Ord.t) => P o0 r)).
    i. des. exists o_top. uipropall. i.
    rr in H0. rr. uipropall. eapply H in H0.
    des. esplits. uipropall. esplits; eauto. rr. uipropall.
  Qed.

  Lemma ord_exist_iProp_mon (P: Ord.t -> iProp)
        (MON: forall o0 o1 (LE: Ord.le o0 o1), bi_entails (P o0) (P o1))
    :
      exists o_top,
        (bi_entails
           (∃ (o: Ord.t), P o)
           (P o_top)).
  Proof.
    hexploit ord_exist_iProp. i. des.
    exists o_top. iIntros "H".
    iPoseProof (H with "H") as (o0) "[H %]".
    iApply MON; eauto.
  Qed.

  Lemma ord_exist_upd (P: Ord.t -> iProp)
    :
      bi_entails
        (#=> ∃ (o: Ord.t), P o)
        (∃ (o1: Ord.t), (#=> (∃ o0, P o0 ∧ ⌜Ord.le o0 o1⌝))).
  Proof.
    hexploit (ord_exist_iProp P). i. des.
    iIntros "H". iExists o_top. iMod "H". iModIntro.
    iPoseProof (H with "H") as "H". eauto.
  Qed.

  Lemma ord_exist_upd_mon (P: Ord.t -> iProp)
        (MON: forall o0 o1 (LE: Ord.le o0 o1), bi_entails (P o0) (P o1))
    :
      bi_entails
        (#=> ∃ (o: Ord.t), P o)
        (∃ (o: Ord.t), (#=> P o)).
  Proof.
    iIntros "H". iPoseProof (ord_exist_upd with "H") as (o1) "H".
    iExists o1. iMod "H". iModIntro. iDestruct "H" as (o0) "[H %]".
    iApply MON; eauto.
  Qed.

  Lemma isim_trivial_upd R
        (Q: R -> iProp)
        itr
    :
      bi_entails
        (#=> (isim_trivial (fun ret => #=> Q ret) itr))
        (isim_trivial Q itr).
  Proof.
    unfold isim_trivial. iIntros "H".
    iPoseProof (ord_exist_upd_mon with "H") as (fuel) "H".
    { i. iIntros "H". iApply isim_flag_mon; eauto. ss. }
    iExists fuel. iMod "H". iApply isim_upd. iModIntro.
    iApply isim_mono; [|iApply "H"]. i. ss.
    iIntros "[> H0 H1]". iModIntro. iFrame.
  Qed.

  Lemma isim_trivial_bind R S
        (Q: S -> iProp)
        (itr: itree Es R) (ktr: _ -> itree Es S)
    :
      bi_entails
        (isim_trivial (fun ret => isim_trivial Q (ktr ret)) itr)
        (isim_trivial Q (itr >>= ktr)).
  Proof.
    unfold isim_trivial. iIntros "H".
    iDestruct "H" as (fuel0) "H".
    hexploit (ord_exist
                (fun ret fuel1 =>
                   forall fuel0,
                     bi_entails
                       (isim
                          world_le_trivial world_wf_trivial mn stb o
                          (bot9, bot9, false, false)
                          (λ (st_src0 st_tgt0 : Any.t) (_ : ()) (ret_tgt0 : S),
                           Q ret_tgt0 ** ⌜st_src0 = Any.upcast tt ∧ st_tgt0 = Any.upcast tt⌝)
                          (Some fuel0) (Any.upcast tt, Ret tt) (Any.upcast tt, ktr ret))
                       (isim
                          world_le_trivial world_wf_trivial mn stb o
                          (bot9, bot9, false, false)
                          (λ (st_src0 st_tgt0 : Any.t) (_ : ()) (ret_tgt0 : S),
                           Q ret_tgt0 ** ⌜st_src0 = Any.upcast tt ∧ st_tgt0 = Any.upcast tt⌝)
                          (Some fuel1) (Any.upcast tt, Ret tt) (Any.upcast tt, ktr ret))
             )).
    i. des.
    iExists (o_top + fuel0)%ord. iApply isim_split_aux.
    iApply isim_mono; [|iApply "H"]. simpl.
    iIntros (? ? ? ?) "[H %]". des; subst.
    hexploit (H ret_tgt).
    { hexploit (ord_exist_iProp_mon (fun o0 =>
                                       isim
                                         world_le_trivial world_wf_trivial mn stb o
                                         (bot9, bot9, false, false)
                                         (λ (st_src0 st_tgt0 : Any.t) (_ : ()) (ret_tgt0 : S),
                                          Q ret_tgt0 ** ⌜st_src0 = Any.upcast tt ∧ st_tgt0 = Any.upcast tt⌝)
                                         (Some o0) (Any.upcast tt, Ret tt) (Any.upcast tt, ktr ret_tgt))).
      { i. iIntros "H". iApply isim_flag_mon; [..|iApply "H"]; ss. }
      i. des. exists o_top0. i.
      iIntros "H". iApply H0. iExists _. eauto.
    }
    i. des. iDestruct "H" as (fuel) "H".
    iPoseProof (H0 with "H") as "H". iApply isim_flag_mon; [..|iApply "H"]; ss.
  Qed.

  Lemma isim_trivial_ret
        R (Q: R -> iProp)
        v
    :
      bi_entails
        (Q v)
        (isim_trivial Q (Ret v)).
  Proof.
    unfold isim_trivial. iIntros "POST".
    iExists (Ord.O). iApply isim_ret. iFrame. auto.
  Qed.

  Lemma isim_trivial_tau
        R
        (Q: R -> iProp)
        itr
    :
      bi_entails
        (isim_trivial Q itr)
        (isim_trivial Q (tau;; itr)).
  Proof.
    unfold isim_trivial. iIntros "H".
    iDestruct "H" as (fuel) "SIM".
    iExists fuel. iApply isim_tau_tgt.
    iApply isim_flag_mon; [..|iApply "SIM"]; ss. refl.
  Qed.

  Lemma isim_trivial_choose
        X
        (Q: X -> iProp)
    :
      bi_entails
        (∀ x, Q x)
        (isim_trivial Q (trigger (Choose X))).
  Proof.
    unfold isim_trivial. iIntros "PRE". iExists Ord.O.
    iApply isim_choose_tgt_trigger. iIntros (x).
    iApply isim_ret. iSplit; auto.
  Qed.

  Lemma isim_trivial_take
        X
        (Q: X -> iProp)
    :
      bi_entails
        (∃ x, Q x)
        (isim_trivial Q (trigger (Take X))).
  Proof.
    unfold isim_trivial. iIntros "PRE". iExists Ord.O.
    iDestruct "PRE" as (x) "PRE".
    iApply isim_take_tgt_trigger. iExists x.
    iApply isim_ret. iSplit; auto.
  Qed.

  Lemma isim_trivial_call
        pre post
        (Q: Any.t -> iProp)
        fn arg_src arg_tgt
        (SPEC: fn_has_spec mn stb o fn arg_src arg_tgt pre post true)
    :
      bi_entails
        ((pre: iProp)
           **
           (∀ ret_src ret_tgt,
               (post ret_src ret_tgt: iProp) -* Q ret_tgt))
        (isim_trivial Q (trigger (Call fn arg_tgt))).
  Proof.
    unfold isim_trivial. iIntros "[PRE RET]".
    iExists (1: Ord.t). iApply isim_call_pure_trigger.
    { eauto. }
    iSplitL "PRE".
    { iSplitR "PRE"; [|auto]. iApply inv_with_current.
      unfold world_wf_trivial. iPureIntro. auto.
    }
    { iIntros (? ? ? ?) "INV PRE".
      iSpecialize ("RET" with "PRE"). iFrame.
      unfold inv_with. iDestruct "INV" as (w1) "[WF _]". auto.
    }
    Unshelve. all: exact tt.
  Qed.

  Lemma isim_trivial_ccallU
        pre post
        A R
        (Q: R -> iProp)
        fn arg_src (arg_tgt: A)
        (SPEC: fn_has_spec mn stb o fn arg_src (Any.upcast arg_tgt) pre post true)
    :
      bi_entails
        ((pre: iProp)
           **
           (∀ ret_src ret_tgt,
               ((post ret_src ret_tgt: iProp)) -* ∃ ret_tgt', ⌜ret_tgt = Any.upcast ret_tgt'⌝ ∧ Q ret_tgt'))
        (isim_trivial Q (ccallU fn arg_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (ccallU fn arg_tgt)).
    unfold isim_trivial. iIntros "[PRE POST]".
    iExists (1: Ord.t). iApply isim_ccallU_pure.
    { eauto. }
    { oauto. }
    iSplitL "PRE".
    { iSplitR "PRE"; auto. iApply inv_with_current.
      unfold world_wf_trivial. auto.
    }
    iIntros (? ? ? ?) "[INV H]".
    iPoseProof ("POST" with "H") as (ret_tgt') "[% POST]".
    iExists ret_tgt'. iSplit; auto. iApply isim_ret.
    unfold inv_with, world_wf_trivial.
    iDestruct "INV" as (w1) "[INV _]". iFrame.
    Unshelve. all: try exact tt.
  Qed.

  Global Instance iProp_isim_trivial_absorbing
         R (Q: R -> iProp)
         itr:
    Absorbing (isim_trivial Q itr).
  Proof.
    unfold Absorbing. unfold bi_absorbingly.
    iIntros "[H0 H1]". iApply isim_trivial_upd.
    iDestruct "H0" as "%". iModIntro.
    iApply isim_trivial_mono; [|iApply "H1"].
    i. ss. iIntros "H". iModIntro. auto.
  Qed.

  Global Instance iProp_isim_trivial_elim_upd
         R (Q: R -> iProp)
         itr
         P:
    ElimModal True false false (#=> P) P (isim_trivial Q itr) (isim_trivial Q itr).
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iApply isim_trivial_upd. iMod "H0". iModIntro.
    iApply isim_trivial_mono; [|iApply "H1"; auto].
    i. ss. iIntros "H". iModIntro. auto.
  Qed.


  Lemma isim_trivial_assume
        (Q: unit -> iProp)
        P
    :
      bi_entails
        (⌜P⌝ ∧ Q tt)
        (isim_trivial Q (assume P)).
  Proof.
    unfold assume. iIntros "[% H1]".
    iApply isim_trivial_bind. iApply isim_trivial_take.
    iExists H. iApply isim_trivial_ret. auto.
  Qed.

  Lemma isim_trivial_guarantee
        (Q: unit -> iProp)
        P
    :
      bi_entails
        (⌜P⌝ -* Q tt)
        (isim_trivial Q (guarantee P)).
  Proof.
    unfold guarantee. iIntros "H".
    iApply isim_trivial_bind. iApply isim_trivial_choose.
    iIntros (H). iApply isim_trivial_ret. iApply "H". auto.
  Qed.

  Lemma isim_trivial_triggerNB
        R
        (Q: R -> iProp)
    :
      bi_entails
        (⌜True⌝)
        (isim_trivial Q (triggerNB)).
  Proof.
    unfold triggerNB. iIntros "_".
    iApply isim_trivial_bind. iApply isim_trivial_choose.
    iIntros ([]).
  Qed.

  Lemma isim_trivial_unwrapU
        R
        (Q: R -> iProp)
        x
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ Q x')
        (isim_trivial Q (unwrapU x)).
  Proof.
    unfold unwrapU. iIntros "H".
    iDestruct "H" as (x') "[% H]". subst.
    iApply isim_trivial_ret. auto.
  Qed.

  Lemma isim_trivial_unwrapN
        R
        (Q: R -> iProp)
        x
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* Q x')
        (isim_trivial Q (unwrapN x)).
  Proof.
    unfold unwrapN. iIntros "H". destruct x.
    { iApply isim_trivial_ret. iApply "H". auto. }
    { iApply isim_trivial_triggerNB. auto. }
  Qed.
End TRIVIAL.
#[export] Hint Resolve world_le_trivial_PreOrder: core.


Require Import OpenDef.

Section ADEQUACY.
  Context `{Σ: GRA.t}.

  Lemma isim_fun_to_tgt_aux
        A wf (le: A -> A -> Prop) `{PreOrder _ le} mn stb
        f_src f_tgt w
        (fsp: fspecbody) x y f st_src st_tgt
        (EQ: x = y)
        (WF: mk_wf wf w (st_src, st_tgt))
        (ISIM: forall w (x: fsp.(meta)) mn_caller arg_src arg_tgt st_src st_tgt,
            bi_entails
              ((inv_with le wf w st_src st_tgt) ** (fsp.(precond) mn_caller x arg_src arg_tgt: iProp))
              (isim
                 le wf mn stb (fsp.(measure) x)
                 (bot9, bot9, true, f_tgt)
                 (fun st_src st_tgt ret_src ret_tgt =>
                    (inv_with le wf w st_src st_tgt) ** (fsp.(postcond) mn_caller x ret_src ret_tgt: iProp))
                 None
                 (st_src, match fsp.(measure) x with
                          | ord_pure _ => _ <- trigger hAPC;; trigger (Choose Any.t)
                          | ord_top => fsp.(fsb_body) (mn_caller, arg_src)
                          end) (st_tgt, f (mn_caller, arg_tgt))))
    :
      sim_itree
        (mk_wf wf) le
        f_src f_tgt
        w
        (st_src, fun_to_tgt mn stb fsp x) (st_tgt, f y).
  Proof.
    subst. destruct y as [mn_caller arg].
    ginit. unfold fun_to_tgt. rewrite HoareFun_parse. harg.
    gfinal. right. eapply hsim_adequacy; auto.
    ginit. eapply isim_init; [clear ACC|eapply ACC]. start_ipm_proof.
    iApply ISIM. iSplitR "PRE"; [|iExact "PRE"].
    iExists w. iSplit; auto.
  Qed.

  Lemma isim_fun_to_tgt
        A wf (le: A -> A -> Prop) `{PreOrder _ le} mn stb
        (fsp: fspecbody) f
        (ISIM: forall w (x: fsp.(meta)) mn_caller arg_src arg_tgt st_src st_tgt,
            bi_entails
              ((inv_with le wf w st_src st_tgt) ** (fsp.(precond) mn_caller x arg_src arg_tgt: iProp))
              (isim
                 le wf mn stb (fsp.(measure) x)
                 (bot9, bot9, true, false)
                 (fun st_src st_tgt ret_src ret_tgt =>
                    (inv_with le wf w st_src st_tgt) ** (fsp.(postcond) mn_caller x ret_src ret_tgt: iProp))
                 None
                 (st_src, match fsp.(measure) x with
                          | ord_pure _ => _ <- trigger hAPC;; trigger (Choose Any.t)
                          | ord_top => fsp.(fsb_body) (mn_caller, arg_src)
                          end) (st_tgt, f (mn_caller, arg_tgt))))
    :
      sim_fsem (mk_wf wf) le
               (fun_to_tgt mn stb fsp) f.
  Proof.
    ii. eapply isim_fun_to_tgt_aux; eauto.
  Qed.

  Lemma isim_fun_to_tgt_open
        A wf (le: A -> A -> Prop) `{PreOrder _ le} mn stb
        (ksp: kspecbody) f
        (FRIEND: forall w (x: ksp.(meta)) mn_caller arg_src arg_tgt st_src st_tgt,
            bi_entails
              ((inv_with le wf w st_src st_tgt) ** (ksp.(precond) mn_caller x arg_src arg_tgt: iProp))
              (isim
                 le wf mn stb (ksp.(measure) x)
                 (bot9, bot9, true, false)
                 (fun st_src st_tgt ret_src ret_tgt =>
                    (inv_with le wf w st_src st_tgt) ** (ksp.(postcond) mn_caller x ret_src ret_tgt: iProp))
                 None
                 (st_src, match ksp.(measure) x with
                          | ord_pure _ => _ <- trigger hAPC;; trigger (Choose Any.t)
                          | ord_top => ksp.(ksb_kbody) (mn_caller, arg_src)
                          end) (st_tgt, f (mn_caller, arg_tgt))))
        (CONTEXT: forall w mn_caller arg st_src st_tgt,
            bi_entails
              (inv_with le wf w st_src st_tgt)
              (isim
                 le wf mn stb ord_top
                 (bot9, bot9, true, false)
                 (fun st_src st_tgt ret_src ret_tgt =>
                    (inv_with le wf w st_src st_tgt ** ⌜ret_src = ret_tgt⌝))
                 None
                 (st_src, ksp.(ksb_ubody) (mn_caller, arg)) (st_tgt, f (mn_caller, arg))))
    :
      sim_fsem (mk_wf wf) le
               (KModSem.disclose_ksb_tgt mn stb ksp) f.
  Proof.
    ii. ginit. unfold KModSem.disclose_ksb_tgt.
    apply sim_itreeC_spec. apply sim_itreeC_take_src. intros [].
    { gfinal. right. eapply isim_fun_to_tgt_aux; eauto. }
    { gfinal. right. eapply isim_fun_to_tgt_aux; eauto. i. ss.
      iIntros "[H0 %]". subst. iApply CONTEXT. auto.
    }
  Qed.

  Lemma isim_fun_to_tgt_open_trivial
        A wf (le: A -> A -> Prop) `{PreOrder _ le} mn stb
        body f
        (CONTEXT: forall w mn_caller arg st_src st_tgt,
            bi_entails
              (inv_with le wf w st_src st_tgt)
              (isim
                 le wf mn stb ord_top
                 (bot9, bot9, true, false)
                 (fun st_src st_tgt ret_src ret_tgt =>
                    (inv_with le wf w st_src st_tgt ** ⌜ret_src = ret_tgt⌝))
                 None
                 (st_src, body (mn_caller, arg)) (st_tgt, f (mn_caller, arg))))
    :
      sim_fsem (mk_wf wf) le
               (KModSem.disclose_ksb_tgt mn stb (ksb_trivial body)) f.
  Proof.
    eapply isim_fun_to_tgt_open; ss; auto. i.
    iIntros "[H0 %]". subst. iApply CONTEXT. iApply "H0".
  Qed.
End ADEQUACY.
