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
    { iIntros "H". iModIntro. iExact "H". }
    { i. iIntros "H". iModIntro. iExact "H". }
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

  Definition isim
             '(r, g, f_src, f_tgt)
             {R_src R_tgt}
             (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
             (fuel: option Ord.t)
             (st_src: Any.t * itree hEs R_src)
             (st_tgt: Any.t * itree Es R_tgt): iProp :=
    fun res =>
      forall ctx (WF: URA.wf (res ⋅ ctx)),
        gpaco9 (_hsim) (cpn9 _hsim) r g _ _ Q ctx fuel f_src f_tgt st_src st_tgt.

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

  Lemma isim_mono R_src R_tgt
        (Q0 Q1: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src itr_src st_tgt itr_tgt
        (MONO: forall st_src st_tgt ret_src ret_tgt,
            (bi_entails (Q0 st_src st_tgt ret_src ret_tgt) (#=> Q1 st_src st_tgt ret_src ret_tgt)))
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) Q0 fuel (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Q1 fuel (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i. hexploit H; eauto. i.
    guclo hmonoC_spec. econs; eauto.
  Qed.

  Lemma isim_wand R_src R_tgt
        (Q0 Q1: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src itr_src st_tgt itr_tgt
    :
      bi_entails
        ((∀ st_src st_tgt ret_src ret_tgt,
             ((Q0 st_src st_tgt ret_src ret_tgt) -∗ (#=> Q1 st_src st_tgt ret_src ret_tgt))) ** (isim (r, g, f_src, f_tgt) Q0 fuel (st_src, itr_src) (st_tgt, itr_tgt)))
        (isim (r, g, f_src, f_tgt) Q1 fuel (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    red in H. unfold Sepconj in H. autorewrite with iprop in H.
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

  Lemma isim_upd R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel f_src f_tgt st_src st_tgt
    :
      bi_entails
        (#=> (isim (r, g, f_src, f_tgt) Q fuel st_src st_tgt))
        (isim (r, g, f_src, f_tgt) Q fuel st_src st_tgt).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    red in H. unfold bi_bupd_bupd in H. ss. unfold Upd in H. autorewrite with iprop in H.
    hexploit H; eauto. i. des.
    hexploit H1; eauto.
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
    unfold isim at 2. i.
    match (type of H) with
    | ?P _ =>
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
    inv ACC. red in IPROP. uipropall. des. subst.
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
    unfold isim at 2. i.
    match (type of H) with
    | ?P _ =>
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
    inv ACC. red in IPROP. uipropall. des. subst. eapply IPROP0.
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
    inv CUR. red in IPROP. uipropall. des.
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
    iDestruct "H0" as "%". iModIntro. iApply "H1".
  Qed.

  Global Instance iProp_isim_elim_upd
         R_src R_tgt r g (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
         fuel f_src f_tgt st_src st_tgt
         P:
    ElimModal True false false (#=> P) P (isim (r, g, f_src, f_tgt) Q fuel st_src st_tgt) (isim (r, g, f_src, f_tgt) Q fuel st_src st_tgt).
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    iApply "H1". iApply "H0".
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
    i. inv CUR. red in IPROP. uipropall. eapply IPROP; eauto.
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
    inv CUR. red in IPROP. uipropall. des. esplits. eapply IPROP; eauto.
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
    inv CUR. red in IPROP. uipropall. i. eapply IPROP; eauto.
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
    inv CUR. red in IPROP. uipropall. i. eapply IPROP; eauto.
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
    inv CUR. red in IPROP. uipropall. des. esplits. eapply IPROP; eauto.
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
