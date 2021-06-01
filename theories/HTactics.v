Require Import Coqlib.
Require Import Universe.
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

Set Implicit Arguments.

#[export] Hint Resolve sim_itree_mon: paco.
#[export] Hint Resolve cpn6_wcompat: paco.

Create HintDb ord_step.
#[export] Hint Resolve Nat.lt_succ_diag_r OrdArith.lt_from_nat OrdArith.lt_add_r: ord_step.
#[export] Hint Extern 1000 => lia: ord_step.





Ltac interp_red := erewrite interp_vis ||
                            erewrite interp_ret ||
                            erewrite interp_tau ||
                            erewrite interp_trigger ||
                            erewrite interp_bind.

Ltac interp_mrec_red := erewrite interp_mrec_hit ||
                                 erewrite interp_mrec_miss ||
                                 erewrite interp_mrec_bind ||
                                 erewrite interp_mrec_tau ||
                                 erewrite interp_mrec_ret.

Ltac interp_state_red := erewrite interp_state_trigger ||
                                  erewrite interp_state_bind ||
                                  erewrite interp_state_tau ||
                                  erewrite interp_state_ret.

Ltac ired_l := try (prw _red_gen 2 1 0).
Ltac ired_r := try (prw _red_gen 1 1 0).

Ltac ired_both := ired_l; ired_r.



(* "safe" simulation constructors *)
Section SIM.

  Context `{Σ: GRA.t}.

  Let st_local: Type := (Σ * Any.t * Σ).
  Let W: Type := (Σ * Any.t) * (Σ * Any.t).
  Variable wf: W -> Prop.



  Variant _safe_sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), Ord.t -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : Ord.t -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | safe_safe_sim_itree_ret
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      (WF: wf (mrs_src0, mrs_tgt0))
      v_src v_tgt
      (RET: RR (mrs_src0, fr_src0) (mrs_tgt0, fr_tgt0) v_src v_tgt)
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), (Ret v_src)) ((mrs_tgt0, fr_tgt0), (Ret v_tgt))
  | safe_safe_sim_itree_tau
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (K: sim_itree _ _ RR i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 (st_src0, tau;; i_src) (st_tgt0, tau;; i_tgt)
  | safe_safe_sim_itree_call
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      fn varg k_src k_tgt
      (WF: wf (mrs_src0, mrs_tgt0))
      (K: forall vret mrs_src1 mrs_tgt1 (WF: wf (mrs_src1, mrs_tgt1)),
          exists i1, sim_itree _ _ RR i1 ((mrs_src1, fr_src0), k_src vret) ((mrs_tgt1, fr_tgt0), k_tgt vret))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Call fn varg) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Call fn varg) >>= k_tgt)
  | safe_safe_sim_itree_syscall
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          exists i1, sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src vret) ((mrs_tgt0, fr_tgt0), k_tgt vret))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Syscall fn varg rvs) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Syscall fn varg rvs) >>= k_tgt)
  (*** TODO: sim_syscall is nontrivial; it should accept "injected" memory... ***)
  (*** TODO: simplify the model: Syscall: list val -> val ***)




  | safe_safe_sim_itree_tau_src
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | safe_safe_sim_itree_take_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: forall (x: X), sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src x) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Take X) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)

  | safe_safe_sim_itree_pput_src
      i0 st_tgt0 fr_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mr0 mp1 mp0
      (K: sim_itree _ _ RR i1 ((mr0, mp1, fr_src0), k_src tt) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mr0, mp0, fr_src0), trigger (PPut mp1) >>= k_src)
                 (st_tgt0, i_tgt)
  | safe_safe_sim_itree_mput_src
      i0 st_tgt0 fr_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mr0 mr1 mp0
      (K: sim_itree _ _ RR i1 ((mr1, mp0, fr_src0), k_src tt) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mr0, mp0, fr_src0), trigger (MPut mr1) >>= k_src)
                 (st_tgt0, i_tgt)
  | safe_safe_sim_itree_fput_src
      i0 mrs_src0 st_tgt0 fr_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      fr_src1
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src1), k_src tt) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (FPut fr_src1) >>= k_src)
                 (st_tgt0, i_tgt)

  | safe_safe_sim_itree_pget_src
      i0 st_tgt0 fr_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mr0 mp0
      (K: sim_itree _ _ RR i1 ((mr0, mp0, fr_src0), k_src mp0) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mr0, mp0, fr_src0), trigger (PGet) >>= k_src)
                 (st_tgt0, i_tgt)
  | safe_safe_sim_itree_mget_src
      i0 fr_src0 st_tgt0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mr0 mp0
      (K: sim_itree _ _ RR i1 ((mr0, mp0, fr_src0), k_src mr0) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mr0, mp0, fr_src0), trigger (MGet) >>= k_src)
                 (st_tgt0, i_tgt)
  | safe_safe_sim_itree_fget_src
      i0 mrs_src0 st_tgt0 fr_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src fr_src0) ((st_tgt0), i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (FGet) >>= k_src)
                 (st_tgt0, i_tgt)






  | safe_safe_sim_itree_tau_tgt
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | safe_safe_sim_itree_choose_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X i_src k_tgt
      (ORD: Ord.lt i1 i0)
      (K: forall (x: X), sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt x))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Choose X) >>= k_tgt)

  | safe_safe_sim_itree_pput_tgt
      i0 st_src0 fr_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      mr0 mp1 mp0
      (K: sim_itree _ _ RR i1 (st_src0, i_src) ((mr0, mp1, fr_tgt0), k_tgt tt))
    :
      _safe_sim_itree sim_itree RR i0 (st_src0, i_src)
                 ((mr0, mp0, fr_tgt0), trigger (PPut mp1) >>= k_tgt)
  | safe_safe_sim_itree_mput_tgt
      i0 st_src0 fr_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      mr0 mr1 mp0
      (K: sim_itree _ _ RR i1 (st_src0, i_src) ((mr1, mp0, fr_tgt0), k_tgt tt))
    :
      _safe_sim_itree sim_itree RR i0 (st_src0, i_src)
                 ((mr0, mp0, fr_tgt0), trigger (MPut mr1) >>= k_tgt)
  | safe_safe_sim_itree_fput_tgt
      i0 mrs_tgt0 st_src0 fr_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      fr_tgt1
      (K: sim_itree _ _ RR i1 (st_src0, i_src) ((mrs_tgt0, fr_tgt1), k_tgt tt))
    :
      _safe_sim_itree sim_itree RR i0 (st_src0, i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FPut fr_tgt1) >>= k_tgt)

  | safe_safe_sim_itree_pget_tgt
      i0 st_src0 fr_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      mr0 mp0
      (K: sim_itree _ _ RR i1 (st_src0, i_src) ((mr0, mp0, fr_tgt0), k_tgt mp0))
    :
      _safe_sim_itree sim_itree RR i0 (st_src0, i_src)
                 ((mr0, mp0, fr_tgt0), trigger (PGet) >>= k_tgt)
  | safe_safe_sim_itree_mget_tgt
      i0 fr_tgt0 st_src0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      mr0 mp0
      (K: sim_itree _ _ RR i1 (st_src0, i_src) ((mr0, mp0, fr_tgt0), k_tgt mr0))
    :
      _safe_sim_itree sim_itree RR i0 (st_src0, i_src)
                 ((mr0, mp0, fr_tgt0), trigger (MGet) >>= k_tgt)
  | safe_safe_sim_itree_fget_tgt
      i0 mrs_tgt0 st_src0 fr_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 ((st_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt fr_tgt0))
    :
      _safe_sim_itree sim_itree RR i0 (st_src0, i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FGet) >>= k_tgt)
  .

  Lemma safe_sim_sim:
    _safe_sim_itree <7= _sim_itree wf.
  Proof.
    i. inv PR; try by (econs; eauto).
  Qed.

End SIM.


Section HLEMMAS.
  Context `{Σ: GRA.t}.
  Local Opaque GRA.to_URA.

  Variant mk_wf (A: Type)
          (R_src: A -> Any.t -> Any.t -> iProp)
          (R_tgt: A -> Any.t -> Any.t -> iProp)
    : (Σ * Any.t) * (Σ * Any.t) -> Prop :=
  | mk_wf_intro
      a
      mr_src mp_src mr_tgt mp_tgt
      (RSRC: R_src a mp_src mp_tgt mr_src)
      (RTGT: R_tgt a mp_src mp_tgt mr_tgt)
    :
      mk_wf R_src R_tgt ((mr_src, mp_src), (mr_tgt, mp_tgt))
  .

  Lemma hcall_clo_ord_weaken' (o_new: Ord.t)
        (fsp1: fspec)
        (o: ord) (x: shelve__ fsp1.(meta))

        A (a0: shelve__ A) FR

        r rg (n: nat) mr_src0 mp_src0 fr_src0
        (fsp0: fspec)
        mr_tgt0 mp_tgt0 frs_tgt k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R_src: A -> Any.t -> Any.t -> iProp) (R_tgt: A -> Any.t -> Any.t -> iProp)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)

        (WEAKER: fspec_weaker fsp1 fsp0)

        ctx0 I
        (ACC: current_iProp ctx0 I)

        (RTGT: R_tgt a0 mp_src0 mp_tgt0 mr_tgt0)

        (UPDATABLE:
           I ⊢ #=> (FR ** R_src a0 mp_src0 mp_tgt0 ** (fsp1.(precond) x varg_src varg_tgt o: iProp)))

        (FUEL: (15 < n)%ord)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1 mr_tgt1 fr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (RTGT: R_tgt a1 mp_src1 mp_tgt1 mr_tgt1)
                      ctx1
                      (ACC: current_iProp ctx1 (FR ** R_src a1 mp_src1 mp_tgt1 ** fsp1.(postcond) x vret_src vret_tgt))
          ,
                gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) rg rg _ _ eqr o_new
                       (mr_src1, mp_src1, fr_src1, k_src (ctx1, vret_src)) (mr_tgt1, mp_tgt1, frs_tgt, k_tgt vret_tgt))
    :
      gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) r rg _ _ eqr n
             (mr_src0, mp_src0, fr_src0, (HoareCall tbr ord_cur fsp0 fn varg_src) ctx0 >>= k_src)
             (mr_tgt0, mp_tgt0, frs_tgt, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    unfold HoareCall, put, discard, forge, checkWf, assume, guarantee.
    ired_both. gstep. econs; [eauto with ord_step|].
    hexploit (WEAKER x). i. des.
    assert (exists mr_src0' rarg_src fr_src0',
               (<<UPDATABLE: URA.wf (ctx0 ⋅ (mr_src0' ⋅ (rarg_src ⋅ fr_src0')))>>) /\
               (<<RSRC: R_src a0 mp_src0 mp_tgt0 mr_src0'>>) /\
               (<<FRS: FR fr_src0'>>) /\
               (<<PRE: fsp0.(precond) x_tgt varg_src varg_tgt o rarg_src>>)).
    { inv ACC. uipropall. hexploit UPDATABLE.
      { eapply URA.wf_mon. eapply GWF. }
      { eapply IPROP. }
      { et. }
      i. des. subst.
      hexploit PRE; et. i. uipropall. hexploit (H0 b); et.
      { eapply URA.wf_mon in H. rewrite URA.add_comm in H. eapply URA.wf_mon in H. auto. }
      { instantiate (1:=a1 ⋅ b0 ⋅ ctx0).
        replace (b ⋅ (a1 ⋅ b0 ⋅ ctx0)) with (a1 ⋅ b0 ⋅ b ⋅ ctx0); auto. r_solve. }
      i. des. esplits; et.
      { replace (ctx0 ⋅ (b0 ⋅ (r1 ⋅ a1))) with (r1 ⋅ (a1 ⋅ b0 ⋅ ctx0)); auto. r_solve. }
    }
    des. exists (mr_src0', URA.add rarg_src fr_src0').
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists rarg_src.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists fr_src0'.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists o.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step).
    { econs; eauto. }
    i. exists (o_new + 20)%ord.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.

    destruct mrs_src1, mrs_tgt1. ss. des.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.
    ired_both; gstep; econs; eauto with ord_step. inv WF.
    ired_both; gstep; econs; eauto with ord_step.
    ired_both; gstep; econs; eauto with ord_step. i.
    ired_both; gstep; econs; eauto with ord_step. i.
    ired_both. guclo lordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    eapply POST; et. hexploit POST0. i.
    uipropall. hexploit (H x0); et.
    { rewrite URA.add_comm in x3. eapply URA.wf_mon in x3.
      rewrite URA.add_comm in x3. eapply URA.wf_mon in x3.
      rewrite URA.add_comm in x3. eapply URA.wf_mon in x3. auto. }
    { instantiate (1:=x2 ⋅ c ⋅ fr_src0').
      replace (x0 ⋅ (x2 ⋅ c ⋅ fr_src0')) with (x2 ⋅ (c ⋅ (fr_src0' ⋅ x0))); auto.
      r_solve. }
    i. des. econs.
    { instantiate (1:=fr_src0' ⋅ c ⋅ r1).
      replace (fr_src0' ⋅ c ⋅ r1 ⋅ x2) with (r1 ⋅ (x2 ⋅ c ⋅ fr_src0')); auto.
      r_solve. }
    esplits; cycle 2; et.
  Qed.

  Lemma hcall_clo_ord_weaken
        Hns Rn Invn
        (o_new: Ord.t)
        (fsp1: fspec)
        (o: ord) (x: shelve__ fsp1.(meta))

        A (a0: shelve__ A)

        r rg (n: nat) mr_src0 mp_src0 fr_src0
        (fsp0: fspec)
        mr_tgt0 mp_tgt0 frs_tgt k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R_src: A -> Any.t -> Any.t -> iProp) (R_tgt: A -> Any.t -> Any.t -> iProp)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)

        (WEAKER: fspec_weaker fsp1 fsp0)

        ctx0 l
        (ACC: current_iPropL ctx0 l)

        (RTGT: R_tgt a0 mp_src0 mp_tgt0 mr_tgt0)

        (UPDATABLE:
           from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R_src a0 mp_src0 mp_tgt0 ** (fsp1.(precond) x varg_src varg_tgt o: iProp)))

        (FUEL: (15 < n)%ord)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1 mr_tgt1 fr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (RTGT: R_tgt a1 mp_src1 mp_tgt1 mr_tgt1)
                      ctx1
                      (ACC: current_iPropL ctx1 ((Invn, R_src a1 mp_src1 mp_tgt1) :: (Rn, fsp1.(postcond) x vret_src vret_tgt) :: snd (alist_pops Hns l)))
          ,
            gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) rg rg _ _ eqr o_new
                   (mr_src1, mp_src1, fr_src1, k_src (ctx1, vret_src)) (mr_tgt1, mp_tgt1, frs_tgt, k_tgt vret_tgt))
    :
      gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) r rg _ _ eqr n
             (mr_src0, mp_src0, fr_src0, (HoareCall tbr ord_cur fsp0 fn varg_src) ctx0 >>= k_src)
             (mr_tgt0, mp_tgt0, frs_tgt, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    eapply hcall_clo_ord_weaken'; et.
    { instantiate (2:=from_iPropL (snd (alist_pops Hns l))).
      etrans.
      { eapply iPropL_alist_pops. }
      iIntros "[H0 H1]".
      iPoseProof (UPDATABLE with "H0") as "> [H0 H2]".
      iModIntro. iFrame.
    }
    i. eapply POST; et. red. ss.
    eapply current_iProp_entail; et.
    iIntros "[[H0 H1] H2]". iFrame.
  Qed.

  Lemma hcall_clo_weaken
        Hns Rn Invn
        (fsp1: fspec)
        (o: ord) (x: shelve__ fsp1.(meta))

        A (a0: shelve__ A)

        r rg (n: nat) mr_src0 mp_src0 fr_src0
        (fsp0: fspec)
        mr_tgt0 mp_tgt0 frs_tgt k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R_src: A -> Any.t -> Any.t -> iProp) (R_tgt: A -> Any.t -> Any.t -> iProp)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)

        (WEAKER: fspec_weaker fsp1 fsp0)

        ctx0 l
        (ACC: current_iPropL ctx0 l)

        (RTGT: R_tgt a0 mp_src0 mp_tgt0 mr_tgt0)

        (UPDATABLE:
           from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R_src a0 mp_src0 mp_tgt0 ** (fsp1.(precond) x varg_src varg_tgt o: iProp)))

        (FUEL: (15 < n)%ord)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1 mr_tgt1 fr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (RTGT: R_tgt a1 mp_src1 mp_tgt1 mr_tgt1)
                      ctx1
                      (ACC: current_iPropL ctx1 (@cons (prod string (bi_car iProp)) (Invn, R_src a1 mp_src1 mp_tgt1) (@cons (prod string (bi_car iProp)) (Rn, fsp1.(postcond) x vret_src vret_tgt) (snd (alist_pops Hns l)))))
          ,
                gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) rg rg _ _ eqr 100
                       (mr_src1, mp_src1, fr_src1, k_src (ctx1, vret_src)) (mr_tgt1, mp_tgt1, frs_tgt, k_tgt vret_tgt))
    :
      gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) r rg _ _ eqr n
             (mr_src0, mp_src0, fr_src0, (HoareCall tbr ord_cur fsp0 fn varg_src) ctx0 >>= k_src)
             (mr_tgt0, mp_tgt0, frs_tgt, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    eapply (@hcall_clo_ord_weaken _ _ _ 100); eauto.
  Qed.

  Lemma hcall_clo
        Hns Rn Invn
        (o: ord) X (x: shelve__ X)
        A (a0: shelve__ A)

        (P: X -> Any.t -> Any.t -> ord -> Σ -> Prop)
        (Q: X -> Any.t -> Any.t -> Σ -> Prop)
        r rg (n: nat) mr_src0 mp_src0 fr_src0
        mr_tgt0 mp_tgt0 frs_tgt k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R_src: A -> Any.t -> Any.t -> iProp) (R_tgt: A -> Any.t -> Any.t -> iProp)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)

        ctx0 l
        (ACC: current_iPropL ctx0 l)

        (RTGT: R_tgt a0 mp_src0 mp_tgt0 mr_tgt0)

        (UPDATABLE:
           from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R_src a0 mp_src0 mp_tgt0 ** (P x varg_src varg_tgt o: iProp)))

        (FUEL: (15 < n)%ord)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1 mr_tgt1 fr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (RTGT: R_tgt a1 mp_src1 mp_tgt1 mr_tgt1)
                      ctx1
                      (ACC: current_iPropL ctx1 (@cons (prod string (bi_car iProp)) (Invn, R_src a1 mp_src1 mp_tgt1) (@cons (prod string (bi_car iProp)) (Rn, Q x vret_src vret_tgt) (snd (alist_pops Hns l)))))
          ,
                gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) rg rg _ _ eqr 100
                       (mr_src1, mp_src1, fr_src1, k_src (ctx1, vret_src)) (mr_tgt1, mp_tgt1, frs_tgt, k_tgt vret_tgt))
    :
      gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) r rg _ _ eqr n
             (mr_src0, mp_src0, fr_src0, (HoareCall tbr ord_cur (mk_fspec P Q) fn varg_src) ctx0 >>= k_src)
             (mr_tgt0, mp_tgt0, frs_tgt, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    eapply hcall_clo_weaken; eauto.
    { refl. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma harg_clo
        Rn Invn
        r rg
        X (P: X -> Any.t -> Any.t -> ord -> Σ -> Prop) varg_tgt
        mr_src mp_src mr_tgt mp_tgt fr_src fr_tgt f_tgt k_src
        A
        (R_src: A -> Any.t -> Any.t -> iProp) (R_tgt: A -> Any.t -> Any.t -> iProp)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        (WF: mk_wf R_src R_tgt ((mr_src, mp_src), (mr_tgt, mp_tgt)))
        (ARG:
           forall a x varg_src ord_cur fr_src
                  (RTGT: R_tgt a mp_src mp_tgt mr_tgt)
                  ctx
                  (ACC: current_iPropL ctx (@cons (prod string (bi_car iProp)) (Rn, P x varg_src varg_tgt ord_cur) (@cons (prod string (bi_car iProp)) (Invn, R_src a mp_src mp_tgt) (@nil (prod string (bi_car iProp)))))),
             gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) rg rg _ _ eqr 89
                    (mr_src, mp_src, fr_src, k_src (ctx, (x, varg_src, ord_cur)))
                    (mr_tgt, mp_tgt, fr_tgt, f_tgt))
    :
      gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) r rg _ _ eqr 100
             (mr_src, mp_src, fr_src, (HoareFunArg P varg_tgt >>= k_src))
             (mr_tgt, mp_tgt, fr_tgt, f_tgt)
  .
  Proof.
    unfold HoareFunArg, put, discard, forge, checkWf, assume, guarantee.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro varg_src.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro x.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro rarg_src.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro VALID.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro ord_cur.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.
    ired_both. inv WF. eapply ARG; et.
    red. econs.
    { instantiate (1:=VALID ⋅ mr_src).
      eapply URA.wf_mon. instantiate (1:=fr_src).
      replace (VALID ⋅ mr_src ⋅ varg_src ⋅ fr_src) with (varg_src ⋅ (mr_src ⋅ (fr_src ⋅ VALID))); et.
      r_solve.
    }
    { ss. red. uipropall. esplits; et.
      { rewrite URA.unit_id. et. }
      { red. uipropall. }
    }
  Qed.

  Lemma hret_clo
        A (a: shelve__ A)
        r rg n mr_src mp_src fr_src
        X (Q: X -> Any.t -> Any.t -> Σ -> Prop)
        x vret_src vret_tgt
        mr_tgt mp_tgt fr_tgt
        (R_src: A -> Any.t -> Any.t -> iProp) (R_tgt: A -> Any.t -> Any.t -> iProp)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        (FUEL: (14 < n)%ord)

        ctx l
        (ACC: current_iPropL ctx l)

        (RTGT: R_tgt a mp_src mp_tgt mr_tgt)

        (UPDATABLE:
           (from_iPropL l) ⊢ #=> (R_src a mp_src mp_tgt ** (Q x vret_src vret_tgt: iProp)))

        (EQ: forall mr_src1 (SAT: R_src a mp_src mp_tgt mr_src1),
            eqr (mr_src1, mp_src, ε) (mr_tgt, mp_tgt, fr_tgt) vret_tgt vret_tgt)
    :
      gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) r rg _ _ eqr n
             (mr_src, mp_src, fr_src, (HoareFunRet Q x (ctx, vret_src)))
             (mr_tgt, mp_tgt, fr_tgt, (Ret vret_tgt))
  .
  Proof.
    unfold HoareFunRet, put, discard, forge, checkWf, assume, guarantee.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists vret_tgt.
    repeat (ired_both; gstep; econs; eauto with ord_step).
    assert (exists mr_src1 rret_src,
               (<<UPDATABLE: URA.wf (ctx ⋅ (mr_src1 ⋅ rret_src))>>) /\
               (<<RSRC: R_src a mp_src mp_tgt mr_src1>>) /\
               (<<PRE: Q x vret_src vret_tgt rret_src>>)).
    { red in ACC. inv ACC. uipropall.
      hexploit (UPDATABLE r0); et.
      { eapply URA.wf_mon; et. }
      i. des. subst. exists a0, b. splits; et.
      replace (ctx ⋅ (a0 ⋅ b)) with (a0 ⋅ b ⋅ ctx); et.
      r_solve.
    }
    des. exists (mr_src1, rret_src).
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). eexists rret_src.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists ε.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    { rewrite URA.unit_id; ss. }
    repeat (ired_both; gstep; econs; eauto with ord_step).
    { econs; et. }
  Qed.

  Lemma APC_start_clo
        (at_most: Ord.t) (n1: Ord.t)
        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx

        (ATMOST: (at_most < kappa)%ord)
        (FUEL: (n1 + 3 < n0)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                       (mr_src0, mp_src0, fr_src0,
                       (interp_hCallE_tgt stb o (_APC at_most) ctx)>>= k_src)
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o APC ctx) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    unfold APC. ired_l. gstep. eapply sim_itree_choose_src.
    { eapply FUEL. }
    exists at_most. ired_l. steps.
    { eauto with ord_step. }
    { unfold guarantee. ired_both. gstep. econs; eauto with ord_step. esplits; eauto.
      ired_both. gstep. econs.
      { instantiate (1:=n1). eapply OrdArith.add_lt_l. rewrite Ord.from_nat_S. eapply Ord.S_pos. }
      ired_both. ss. }
  Unshelve.
    all: ss.
  Qed.

  Lemma APC_stop_clo
        (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx

        (FUEL: (n1 + 1 < n0)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                      (mr_src0, mp_src0, fr_src0, k_src (ctx, ()))
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (_APC at_most) ctx) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APC. ired_l. gstep. eapply sim_itree_choose_src.
    { eapply FUEL. }
    exists true. ired_l. gstep. eapply sim_itree_tau_src.
    { eapply OrdArith.add_lt_l. rewrite Ord.from_nat_S. eapply Ord.S_pos. }
    ired_both. auto.
  Qed.

  Lemma APC_step_clo
        (fn: gname) (args: Any.t) (next: Ord.t) (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src ctx0
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (FUEL: (n1 + 7 < n0)%ord)
        (fsp: fspec)
        (FIND: alist_find fn stb = Some fsp)
        (NEXT: (next < at_most)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                      (mr_src0, mp_src0, fr_src0,
                       ('(ctx1, _) <- (HoareCall true o fsp fn args ctx0);;
                        Tau (ITree.bind (interp_hCallE_tgt stb o (_APC next) ctx1) k_src)))
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
             (mr_src0, mp_src0, fr_src0, (interp_hCallE_tgt stb o (_APC at_most) ctx0) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APC. ired_l. gstep. eapply sim_itree_choose_src.
    { eapply FUEL. }
    exists false. ired_l. gstep. eapply sim_itree_tau_src.
    { eapply OrdArith.lt_add_r. eauto with ord_step. }
    ired_l. gstep. eapply sim_itree_choose_src.
    { eapply OrdArith.lt_add_r. eauto with ord_step. }
    exists next. ired_l. gstep. eapply sim_itree_tau_src.
    { eapply OrdArith.lt_add_r. eauto with ord_step. }
    ired_l. unfold guarantee. ired_l. gstep. eapply sim_itree_choose_src.
    { eapply OrdArith.lt_add_r. eauto with ord_step. }
    split.
    { auto. }
    ired_l. gstep. eapply sim_itree_tau_src.
    { eapply OrdArith.lt_add_r. eauto with ord_step. }
    ired_l. gstep. eapply sim_itree_choose_src.
    { eapply OrdArith.lt_add_r. eauto with ord_step. }
    exists (fn, args).
    ired_l. gstep. eapply sim_itree_tau_src.
    { eapply OrdArith.add_lt_l. rewrite Ord.from_nat_S. eapply Ord.S_pos. }
    ired_l. ss. rewrite FIND. ss. subst. ired_l.
    ss. ired_l.
    match goal with
    | [SIM: gpaco6 _ _ _ _ _ _ _ _ ?i0 _ |- gpaco6 _ _ _ _ _ _ _ _ ?i1 _] =>
      replace i1 with i0; auto
    end.
    f_equal. grind.
  Qed.

End HLEMMAS.


(* main tactics *)

(* Ltac init := *)
(*   split; ss; ii; clarify; rename y into varg; eexists 100%nat; ss; des; clarify; *)
(*   ginit; asimpl; *)
(*   try (unfold fun_to_tgt, cfun; rewrite HoareFun_parse); ss. *)

(* TODO: init with user given ordinal *)

Ltac prep := ired_both.

Ltac force_l :=
  prep;
  match goal with
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, guarantee ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; gstep; eapply sim_itree_choose_src; [eauto with ord_step|exists name]|contradict name]; cycle 1

  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, ITree.bind' _ (interp _ guarantee ?P) (_, _))) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; gstep; eapply sim_itree_choose_src; [eauto with ord_step|exists name]|contradict name]; cycle 1

   (* TODO: handle interp_hCallE_tgt better and remove this case *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, ITree.bind' _ (interp _ (guarantee ?P ))) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; gstep; eapply sim_itree_choose_src; [eauto with ord_step|exists name]|contradict name]; cycle 1; clear name

  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_tgt; gstep; econs; eauto with ord_step; unseal i_tgt
  end
.

Ltac force_r :=
  prep;
  match goal with
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    destruct (classic P) as [name|name]; [ired_both; gstep; eapply sim_itree_take_tgt; [eauto with ord_step|exists name]|contradict name]; cycle 1

  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_src; gstep; econs; eauto with ord_step; unseal i_src
  end
.

Ltac _step :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; force_l; ss; fail]
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_both; gstep; eapply sim_itree_take_src; [eapply OrdArith.lt_from_nat; apply Nat.lt_succ_diag_r|]; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; force_r; ss; fail]
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_both; gstep; eapply sim_itree_choose_tgt; [eapply OrdArith.lt_from_nat; apply Nat.lt_succ_diag_r|]; intro name



  | _ => (*** default ***)
    gstep; eapply safe_sim_sim; econs; try (eapply OrdArith.lt_from_nat; apply Nat.lt_succ_diag_r); i
  end;
  (* idtac *)
  match goal with
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.
Ltac steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) unfold alist_add; simpl; des_ifs_safe).

Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 tgt1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco6 (_sim_itree wf) _ _ _ _ _ _ n ((src0, src1), src2) ((tgt0, tgt1), tgt2))
      (at level 60,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' tgt1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Ltac _harg_tac := prep; eapply harg_clo; i.

Ltac _hcall_tac x o mr_src1 fr_src1 rarg_src := prep; eapply (@hcall_clo _ mr_src1 fr_src1 rarg_src o _ x); [|eapply OrdArith.lt_from_nat; lia|..].

Ltac _hret_tac mr_src1 rret_src := prep; eapply (@hret_clo _ mr_src1 rret_src); [eapply OrdArith.lt_from_nat; lia|..].

Require Import TODOYJ.

Ltac astep_full _fn _args _next _n1 :=
  eapply (@APC_step_clo _ _fn _ _args _next _n1);
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; lia)]))|
   (try by (stb_tac; refl))|
   (eapply OrdArith.lt_from_nat; lia)|
  ].

Ltac astep _fn _args :=
  eapply (@APC_step_clo _ _fn _ _args);
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
   (try by (stb_tac; refl))|
   (eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r)|
  ].

Ltac acatch :=
  match goal with
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn (Any.upcast ?args)) >>= _)) ] =>
    astep fn args
  end.

Ltac astop :=
  eapply APC_stop_clo;
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|].

Ltac astart _at_most :=
  eapply (@APC_start_clo _ _at_most);
  [eauto with ord_kappa|
   (try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
  ]
.

(* Ltac harg_tac := *)
(*   _harg_tac; *)
(*   match goal with *)
(*   | [H: URA.wf ?cur |- _] => *)
(*     let name := fresh "GWF" in *)
(*     assert(name: __gwf_mark__ cur cur) by (split; [refl|exact H]); clear H *)
(*   end. *)

(* Ltac hcall_tac x o MR_SRC1 FR_SRC1 RARG_SRC := *)
(*   let mr_src1 := r_gather MR_SRC1 in *)
(*   let fr_src1 := r_gather FR_SRC1 in *)
(*   let rarg_src := r_gather RARG_SRC in *)
(*   let tac0 := try by (eapply URA.extends_updatable; r_equalize; r_solve) in *)
(*   let tac1 := (on_gwf ltac:(fun H => clear H); *)
(*                let WF := fresh "WF" in *)
(*                let tmp := fresh "_tmp_" in *)
(*                let GWF := fresh "GWF" in *)
(*                intros ? ? ? ? ? WF; cbn in WF; desH WF; subst; *)
(*                esplits; ss; et; intros tmp ?; assert(GWF: ☀) by (split; [refl|exact tmp]); clear tmp; iRefresh; iClears') in *)
(*   prep; *)
(*   (match x with *)
(*    | ltac_wild => *)
(*      match o with *)
(*      | ltac_wild => eapply (@hcall_clo _ mr_src1 fr_src1 rarg_src) *)
(*      | _ => eapply (@hcall_clo _ mr_src1 fr_src1 rarg_src o) *)
(*      end *)
(*    | _ => eapply (@hcall_clo _ mr_src1 fr_src1 rarg_src o _ x) *)
(*    end); *)
(*   shelve_goal; [on_gwf ltac:(fun GWF => apply GWF)|tac0|eapply OrdArith.lt_from_nat; lia|..|tac1] *)
(* . *)

(* Ltac hcall_tac_weaken fsp x o MR_SRC1 FR_SRC1 RARG_SRC := *)
(*   let mr_src1 := r_gather MR_SRC1 in *)
(*   let fr_src1 := r_gather FR_SRC1 in *)
(*   let rarg_src := r_gather RARG_SRC in *)
(*   let tac0 := try by (eapply URA.extends_updatable; r_equalize; r_solve) in *)
(*   (* let tac0 := etrans; [etrans; [|on_gwf ltac:(fun GWF => apply GWF)]|]; eapply URA.extends_updatable; r_equalize; r_solve; fail in *) *)
(*   let tac1 := (on_gwf ltac:(fun H => clear H); *)
(*                let WF := fresh "WF" in *)
(*                let tmp := fresh "_tmp_" in *)
(*                let GWF := fresh "GWF" in *)
(*                intros ? ? ? ? ? WF; cbn in WF; desH WF; subst; *)
(*                esplits; ss; et; intros tmp ?; assert(GWF: ☀) by (split; [refl|exact tmp]); clear tmp; iRefresh; iClears') in *)
(*   prep; *)
(*   (match x with *)
(*    | ltac_wild => *)
(*      match o with *)
(*      | ltac_wild => eapply (@hcall_clo_weaken _ _ _ fsp mr_src1 fr_src1 rarg_src) *)
(*      | _ => eapply (@hcall_clo_weaken _ _ _ fsp mr_src1 fr_src1 rarg_src o) *)
(*      end *)
(*    | _ => eapply (@hcall_clo_weaken _ _ _ fsp mr_src1 fr_src1 rarg_src o x) *)
(*    end); *)
(*   shelve_goal; [|on_gwf ltac:(fun GWF => apply GWF)|tac0|eapply OrdArith.lt_from_nat; lia|..|tac1] *)
(* . *)

(* Ltac hret_tac MR_SRC RT_SRC := *)
(*   let mr_src1 := r_gather MR_SRC in *)
(*   let fr_src1 := r_gather RT_SRC in *)
(*   let tac0 := try by (eapply URA.extends_updatable; r_equalize; r_solve) in *)
(*   _hret_tac mr_src1 fr_src1; [on_gwf ltac:(fun GWF => apply GWF)|tac0| | |try refl] *)
(* . *)

(* Ltac acall_tac A0 A1 A2 A3 A4 := *)
(*   acatch; [..|hcall_tac A0 A1 A2 A3 A4]. *)

(* Ltac acall_tac_weaken fsp A0 A1 A2 A3 A4 := *)
(*   acatch; [..|hcall_tac_weaken fsp A0 A1 A2 A3 A4]. *)

Ltac init :=
  let varg_src := fresh "varg_src" in
  let varg := fresh "varg" in
  let EQ := fresh "EQ" in
  let mr_src := fresh "mr_src" in
  let mp_src := fresh "mp_src" in
  let mr_tgt := fresh "mr_tgt" in
  let mp_tgt := fresh "mp_tgt" in
  let WF := fresh "WF" in
  split; ss; intros varg_src varg EQ [mr_src mp_src] [mr_tgt mp_tgt] WF;
  (try subst varg_src); exists 100; cbn;
  ginit;
  try (unfold fun_to_tgt, cfun; rewrite HoareFun_parse); simpl.

Ltac harg :=
  let PRE := constr:("PRE") in
  let INV := constr:("INV") in
  eapply (@harg_clo _ PRE INV);
  [eassumption
  |
  ]; i.

Tactic Notation "hret" uconstr(a) :=
  eapply (@hret_clo _ _ a); unshelve_goal;
  [eauto with ord_step
  |eassumption
  |
  |start_ipm_proof
  |
  ].

Tactic Notation "hcall" uconstr(o) uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let Hns := select_ihyps Hns in
  eapply (@hcall_clo _ Hns POST INV o _ x _ a);
  unshelve_goal;
  [eassumption
  |
  |start_ipm_proof
  |eauto with ord_step
  |
  |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H)
  ].

Tactic Notation "hcall_weaken" uconstr(fsp) uconstr(o) uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let Hns := select_ihyps Hns in
  eapply (@hcall_clo_weaken _ Hns POST INV _ _ fsp o _ x _ a);
  unshelve_goal;
  [
  |eassumption
  |
  |start_ipm_proof
  |eauto with ord_step
  |
  |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H)
  ].

Global Opaque _APC APC interp interp_hCallE_tgt.

Global Opaque HoareFunArg HoareFunRet.

Definition __hide_mark A (a : A) : A := a.
Lemma intro_hide_mark: forall A (a: A), a = __hide_mark a. refl. Qed.

Ltac hide_k :=
  match goal with
  | [ |- (gpaco6 _ _ _ _ _ _ _ _ (_, ?isrc >>= ?ksrc) (_, ?itgt >>= ?ktgt)) ] =>
    erewrite intro_hide_mark with (a:=ksrc);
    erewrite intro_hide_mark with (a:=ktgt);
    let name0 := fresh "__KSRC__" in set (__hide_mark ksrc) as name0; move name0 at top;
    let name0 := fresh "__KTGT__" in set (__hide_mark ktgt) as name0; move name0 at top
  end.

Ltac unhide_k :=
  do 2 match goal with
  | [ H := __hide_mark _ |- _ ] => subst H
  end;
  rewrite <- ! intro_hide_mark
.
