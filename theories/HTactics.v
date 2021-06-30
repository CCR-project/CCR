Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef STB SimModSemL SimModSemHint.

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
#[export] Hint Resolve cpn7_wcompat: paco.

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

  Context `{ns: gnames}.

  Variable world: Type.

  Let st_local: Type := (Any.t).
  Let W: Type := (Any.t) * (Any.t).

  Variable wf: world -> W -> Prop.
  Variable le: relation world.


  Variant _safe_sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), Ord.t -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : Ord.t -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | safe_sim_itree_ret
      i0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      _safe_sim_itree sim_itree RR i0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | safe_sim_itree_tau
      i0 w0 st_src0 st_tgt0
      i1 i_src i_tgt
      (K: sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 w0 (st_src0, tau;; i_src) (st_tgt0, tau;; i_tgt)
  | safe_sim_itree_call
      i0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          exists i1, sim_itree _ _ RR i1 w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      _safe_sim_itree sim_itree RR i0 w (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | safe_sim_itree_syscall
      i0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          exists i1, sim_itree _ _ RR i1 w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _safe_sim_itree sim_itree RR i0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)
  (*** TODO: sim_syscall is nontrivial; it should accept "injected" memory... ***)
  (*** TODO: simplify the model: Syscall: list val -> val ***)



  | safe_sim_itree_tau_src
      i0 w0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | safe_sim_itree_take_src
      i0 w0 st_src0 st_tgt0
      i1 X k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: forall (x: X), sim_itree _ _ RR i1 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 w0 (st_src0, trigger (Take X) >>= k_src)
                 (st_tgt0, i_tgt)

  | safe_sim_itree_pput_src
      i0 w0 st_tgt0 st_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      st_src1
      (K: sim_itree _ _ RR i1 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                 (st_tgt0, i_tgt)

  | safe_sim_itree_pget_src
      i0 w0 st_tgt0 st_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 w0 (st_src0, trigger (PGet) >>= k_src)
                 (st_tgt0, i_tgt)






  | safe_sim_itree_tau_tgt
      i0 w0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | safe_sim_itree_choose_tgt
      i0 w0 st_src0 st_tgt0
      i1 X i_src k_tgt
      (ORD: Ord.lt i1 i0)
      (K: forall (x: X), sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _safe_sim_itree sim_itree RR i0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Choose X) >>= k_tgt)

  | safe_sim_itree_pput_tgt
      i0 w0 st_src0 st_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      st_tgt1
      (K: sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
      _safe_sim_itree sim_itree RR i0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | safe_sim_itree_pget_tgt
      i0 w0 st_src0 st_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
      _safe_sim_itree sim_itree RR i0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PGet) >>= k_tgt)
  .

  Lemma safe_sim_sim:
    _safe_sim_itree <8= _sim_itree wf le.
  Proof.
    i. inv PR; try by (econs; eauto).
  Qed.

End SIM.


Section HLEMMAS.
  Context `{Σ: GRA.t} `{ns: gnames}.
  Local Opaque GRA.to_URA.

  Variant mk_wf (A: Type)
          (R: A -> Any.t -> Any.t -> iProp)
    : A -> Any.t * Any.t -> Prop :=
  | mk_wf_intro
      a
      mr_src mp_src mp_tgt
      (RSRC: URA.wf mr_src -> R a mp_src mp_tgt mr_src)
    :
      mk_wf R a ((Any.pair mp_src mr_src↑), mp_tgt)
  .

  Lemma hcall_clo_ord_weaken' (o_new: Ord.t)
        (fsp1: fspec)
        (o: ord) (x: shelve__ fsp1.(meta))

        A (a0: shelve__ A) FR

        (le: A -> A -> Prop) mn r rg a (n: nat) mr_src0 mp_src0 fr_src0
        (fsp0: fspec)
        mp_tgt0 k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        (WEAKER: fspec_weaker fsp1 fsp0)

        ctx0 I
        (ACC: current_iProp ctx0 I)

        (UPDATABLE:
           I ⊢ #=> (FR ** R a0 mp_src0 mp_tgt0 ** (fsp1.(precond) (Some mn) x varg_src varg_tgt o: iProp)))

        (FUEL: (15 < n)%ord)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1 fr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      ctx1
                      (ACC: current_iProp ctx1 (FR ** R a1 mp_src1 mp_tgt1 ** fsp1.(postcond) (Some mn) x vret_src vret_tgt))
          ,
                gpaco7 (_sim_itree (mk_wf R) le) (cpn7 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_new a
                       (Any.pair mp_src1 mr_src1↑, k_src (ctx1, fr_src1, vret_src)) (mp_tgt1, k_tgt vret_tgt))
    :
      gpaco7 (_sim_itree (mk_wf R) le) (cpn7 (_sim_itree (mk_wf R) le)) r rg _ _ eqr n a
             (Any.pair mp_src0 mr_src0, (HoareCall mn tbr ord_cur fsp0 fn varg_src) (ctx0, fr_src0) >>= k_src)
             (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    unfold HoareCall, mput, mget, assume, guarantee.
    ired_both. gstep. econs; [eauto with ord_step|].
    hexploit (WEAKER x). i. des.
    assert (exists mr_src0' rarg_src fr_src0',
               (<<UPDATABLE: URA.wf (ctx0 ⋅ (mr_src0' ⋅ (rarg_src ⋅ fr_src0')))>>) /\
               (<<RSRC: R a0 mp_src0 mp_tgt0 mr_src0'>>) /\
               (<<FRS: FR fr_src0'>>) /\
               (<<PRE: fsp0.(precond) (Some mn) x_tgt varg_src varg_tgt o rarg_src>>)).
    { inv ACC. uipropall. hexploit UPDATABLE.
      { eapply URA.wf_mon. eapply GWF. }
      { eapply IPROP. }
      { et. }
      i. des. subst.
      hexploit PRE; et. i. uipropall. hexploit (H0 b); et.
      { eapply URA.wf_mon in H. rewrite URA.add_comm in H. eapply URA.wf_mon in H. auto. }
      { instantiate (1:=a2 ⋅ b0 ⋅ ctx0).
        replace (b ⋅ (a2 ⋅ b0 ⋅ ctx0)) with (a2 ⋅ b0 ⋅ b ⋅ ctx0); auto. r_solve. }
      i. des. esplits; et.
      { replace (ctx0 ⋅ (b0 ⋅ (r1 ⋅ a2))) with (r1 ⋅ (a2 ⋅ b0 ⋅ ctx0)); auto. r_solve. }
    }
    des. exists (rarg_src, fr_src0', mr_src0').
    repeat (ired_both; gstep; econs; eauto with ord_step).
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    { r_wf UPDATABLE0. }
    repeat (ired_both; gstep; econs; eauto with ord_step). exists x_tgt.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists varg_tgt.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists o.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step).
    { econs; eauto. }
    i. exists (o_new + 20)%ord.
    repeat (ired_both; gstep; econs; eauto with ord_step). i. destruct x0.
    repeat (ired_both; gstep; econs; eauto with ord_step). inv WF.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.
    ired_both. guclo lordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    eapply POST; et. hexploit POST0. i.
    uipropall. hexploit (H c); et.
    { eapply URA.wf_mon. instantiate (1:=fr_src0' ⋅ c0 ⋅ mr_src). r_wf x0. }
    { instantiate (1:=fr_src0' ⋅ c0 ⋅ mr_src). r_wf x0. }
    i. des. econs.
    { instantiate (1:=fr_src0' ⋅ mr_src ⋅ r1). r_wf H0. }
    esplits; et.
    eapply RSRC0.
    eapply URA.wf_mon. instantiate (1:=r1 ⋅ fr_src0' ⋅ c0). r_wf H0.
  Qed.

  Lemma hcall_clo_ord_weaken
        Hns Rn Invn
        (o_new: Ord.t)
        (fsp1: fspec)
        (o: ord) (x: shelve__ fsp1.(meta))

        A (a0: shelve__ A)

        (le: A -> A -> Prop) mn r rg a (n: nat) mr_src0 mp_src0 fr_src0
        (fsp0: fspec)
        mp_tgt0 k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        (WEAKER: fspec_weaker fsp1 fsp0)

        ctx0 l
        (ACC: current_iPropL ctx0 l)

        (UPDATABLE:
           from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R a0 mp_src0 mp_tgt0 ** (fsp1.(precond) (Some mn) x varg_src varg_tgt o: iProp)))

        (FUEL: (15 < n)%ord)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1 fr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      ctx1
                      (ACC: current_iPropL ctx1 ((Invn, R a1 mp_src1 mp_tgt1) :: (Rn, fsp1.(postcond) (Some mn) x vret_src vret_tgt) :: snd (alist_pops Hns l)))
          ,
            gpaco7 (_sim_itree (mk_wf R) le) (cpn7 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_new a
                   (Any.pair mp_src1 mr_src1↑, k_src (ctx1, fr_src1, vret_src)) (mp_tgt1, k_tgt vret_tgt))
    :
      gpaco7 (_sim_itree (mk_wf R) le) (cpn7 (_sim_itree (mk_wf R) le)) r rg _ _ eqr n a
             (Any.pair mp_src0 mr_src0, (HoareCall mn tbr ord_cur fsp0 fn varg_src) (ctx0, fr_src0) >>= k_src)
             (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    eapply hcall_clo_ord_weaken'; et.
    { instantiate (3:=from_iPropL (snd (alist_pops Hns l))).
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

        (le: A -> A -> Prop) mn r rg a (n: nat) mr_src0 mp_src0 fr_src0
        (fsp0: fspec)
        mp_tgt0 k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        (WEAKER: fspec_weaker fsp1 fsp0)

        ctx0 l
        (ACC: current_iPropL ctx0 l)

        (UPDATABLE:
           from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R a0 mp_src0 mp_tgt0 ** (fsp1.(precond) (Some mn) x varg_src varg_tgt o: iProp)))

        (FUEL: (15 < n)%ord)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1 fr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      ctx1
                      (ACC: current_iPropL ctx1 (@cons (prod string (bi_car iProp)) (Invn, R a1 mp_src1 mp_tgt1) (@cons (prod string (bi_car iProp)) (Rn, fsp1.(postcond) (Some mn) x vret_src vret_tgt) (snd (alist_pops Hns l)))))
          ,
            gpaco7 (_sim_itree (mk_wf R) le) (cpn7 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr 100 a
                   (Any.pair mp_src1 mr_src1↑, k_src (ctx1, fr_src1, vret_src)) (mp_tgt1, k_tgt vret_tgt))
    :
      gpaco7 (_sim_itree (mk_wf R) le) (cpn7 (_sim_itree (mk_wf R) le)) r rg _ _ eqr n a
             (Any.pair mp_src0 mr_src0, (HoareCall mn tbr ord_cur fsp0 fn varg_src) (ctx0, fr_src0) >>= k_src)
             (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    eapply (@hcall_clo_ord_weaken _ _ _ 100); eauto.
  Qed.

  Lemma hcall_clo
        Hns Rn Invn
        (o: ord) X (x: shelve__ X)
        A (a0: shelve__ A)

        (P: option mname -> X -> Any.t -> Any.t -> ord -> Σ -> Prop)
        (Q: option mname -> X -> Any.t -> Any.t -> Σ -> Prop)
        (le: A -> A -> Prop) mn r rg a (n: nat) mr_src0 mp_src0 fr_src0
        mp_tgt0 k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        ctx0 l
        (ACC: current_iPropL ctx0 l)

        (UPDATABLE:
           from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R a0 mp_src0 mp_tgt0 ** (P (Some mn) x varg_src varg_tgt o: iProp)))

        (FUEL: (15 < n)%ord)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1 fr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      ctx1
                      (ACC: current_iPropL ctx1 (@cons (prod string (bi_car iProp)) (Invn, R a1 mp_src1 mp_tgt1) (@cons (prod string (bi_car iProp)) (Rn, Q (Some mn) x vret_src vret_tgt) (snd (alist_pops Hns l)))))
          ,
                gpaco7 (_sim_itree (mk_wf R) le) (cpn7 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr 100 a
                       (Any.pair mp_src1 mr_src1↑, k_src (ctx1, fr_src1, vret_src)) (mp_tgt1, k_tgt vret_tgt))
    :
      gpaco7 (_sim_itree (mk_wf R) le) (cpn7 (_sim_itree (mk_wf R) le)) r rg _ _ eqr n a
             (Any.pair mp_src0 mr_src0, (HoareCall mn tbr ord_cur (mk_fspec P Q) fn varg_src) (ctx0, fr_src0) >>= k_src)
             (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    eapply hcall_clo_weaken; eauto.
    { refl. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma harg_clo
        A Rn Invn
        mn r rg
        X (P: option mname -> X -> Any.t -> Any.t -> ord -> Σ -> Prop) varg
        mpr_src mp_tgt f_tgt k_src
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (WF: mk_wf R a (mpr_src, mp_tgt))
        (ARG:
           forall x varg_src ord_cur fr_src
                  ctx (mr_src: Σ) mp_src
                  (ACC: current_iPropL ctx (@cons (prod string (bi_car iProp)) (Rn, P mn x varg_src varg ord_cur) (@cons (prod string (bi_car iProp)) (Invn, R a mp_src mp_tgt) (@nil (prod string (bi_car iProp)))))),
             gpaco7 (_sim_itree (mk_wf R) le) (cpn7 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr 93 a
                    (Any.pair mp_src mr_src↑, k_src (ctx, fr_src, ((mn, x), varg_src, ord_cur)))
                    (mp_tgt, f_tgt))
    :
      gpaco7 (_sim_itree (mk_wf R) le) (cpn7 (_sim_itree (mk_wf R) le)) r rg _ _ eqr 100 a
             (mpr_src, (HoareFunArg P (mn, varg) >>= k_src))
             (mp_tgt, f_tgt)
  .
  Proof.
    inv WF.
    unfold HoareFunArg, mput, mget, assume, guarantee.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro x.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro varg_src.
    repeat (ired_both; gstep; econs; eauto with ord_step). intros (rarg_src, ctx).
    repeat (ired_both; gstep; econs; eauto with ord_step).
    repeat (ired_both; gstep; econs; eauto with ord_step). intro VALID.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro ord_cur.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.
    ired_both. eapply ARG; et.
    red. econs.
    { instantiate (1:=rarg_src ⋅ mr_src). r_wf VALID. }
    { ss. red. uipropall. esplits; et.
      { rewrite URA.unit_id. et. }
      { eapply RSRC; et. eapply URA.wf_mon. instantiate (1:=(ctx ⋅ rarg_src)). r_wf VALID. }
      { red. uipropall. }
    }
  Qed.

  Lemma hret_clo
        A (a: shelve__ A)
        mn r rg n mr_src mp_src fr_src a0
        X (Q: option mname -> X -> Any.t -> Any.t -> Σ -> Prop)
        x vret_src vret_tgt
        mp_tgt
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (FUEL: (14 < n)%ord)

        ctx l
        (ACC: current_iPropL ctx l)

        (WLE: le a0 a)

        (UPDATABLE:
           (from_iPropL l) ⊢ #=> (R a mp_src mp_tgt ** (Q mn x vret_src vret_tgt: iProp)))

        (EQ: forall (mr_src1: Σ) (WLE: le a0 a) (WF: mk_wf R a (Any.pair mp_src mr_src1↑, mp_tgt)),
            eqr (Any.pair mp_src mr_src1↑) mp_tgt vret_tgt vret_tgt)
    :
      gpaco7 (_sim_itree (mk_wf R) le) (cpn7 (_sim_itree (mk_wf R) le)) r rg _ _ eqr n a0
             (Any.pair mp_src mr_src, (HoareFunRet Q mn x (ctx, fr_src, vret_src)))
             (mp_tgt, (Ret vret_tgt))
  .
  Proof.
    unfold HoareFunRet, mput, mget, guarantee.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists vret_tgt.
    repeat (ired_both; gstep; econs; eauto with ord_step).
    assert (exists mr_src1 rret_src,
               (<<UPDATABLE: URA.wf (ctx ⋅ (mr_src1 ⋅ rret_src))>>) /\
               (<<RSRC: R a mp_src mp_tgt mr_src1>>) /\
               (<<PRE: Q mn x vret_src vret_tgt rret_src>>)).
    { red in ACC. inv ACC. uipropall.
      hexploit (UPDATABLE r0); et.
      { eapply URA.wf_mon; et. }
      i. des. subst. exists a1, b. splits; et.
      replace (ctx ⋅ (a1 ⋅ b)) with (a1 ⋅ b ⋅ ctx); et.
      r_solve.
    }
    des. exists (rret_src, mr_src1).
    repeat (ired_both; gstep; econs; eauto with ord_step).
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits.
    { r_wf UPDATABLE0. }
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step).
    eapply EQ; et. econs; et.
  Qed.

  Lemma APC_start_clo
        (at_most: Ord.t) (n1: Ord.t)
        (o: ord)
        A mn r rg a (n0: Ord.t) mp_src0
        k_src
        (wf: A -> Any.t * Any.t -> Prop)
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx

        (ATMOST: (at_most < kappa)%ord)
        (FUEL: (n1 + 3 < n0)%ord)

        (POST: gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) rg rg _ _ eqr n1 a
                      (mp_src0,
                       (interp_hCallE_tgt mn stb o (_APC at_most) ctx)>>= k_src)
                      (itr_tgt))
    :
      gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) r rg _ _ eqr n0 a
             (mp_src0,
              (interp_hCallE_tgt mn stb o APC ctx) >>= k_src)
             (itr_tgt).
  Proof.
    unfold APC. destruct ctx. destruct itr_tgt.
    ired_both. gstep. eapply sim_itree_choose_src.
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
        A mn r rg a (n0: Ord.t) mp_src0
        k_src
        (at_most: Ord.t)
        (wf: A -> Any.t * Any.t -> Prop)
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx

        (FUEL: (n1 + 1 < n0)%ord)

        (POST: gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) rg rg _ _ eqr n1 a
                      (mp_src0, k_src (ctx, ()))
                      (itr_tgt))
    :
      gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) r rg _ _ eqr n0 a
              (mp_src0,
              (interp_hCallE_tgt mn stb o (_APC at_most) ctx) >>= k_src)
             (itr_tgt).
  Proof.
    destruct ctx. destruct itr_tgt.
    rewrite unfold_APC. ired_l. gstep. eapply sim_itree_choose_src.
    { eapply FUEL. }
    exists true. ired_l. gstep. eapply sim_itree_tau_src.
    { eapply OrdArith.add_lt_l. rewrite Ord.from_nat_S. eapply Ord.S_pos. }
    ired_both. auto.
  Qed.

  Lemma APC_step_clo
        (fn: gname) (args: Any.t) (next: Ord.t) (n1: Ord.t)

        (o: ord)
        A mn r rg a (n0: Ord.t) mp_src0
        k_src ctx0
        (at_most: Ord.t)
        (wf: A -> Any.t * Any.t -> Prop)
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (FUEL: (n1 + 7 < n0)%ord)
        (fsp: fspec)
        (FIND: stb fn = Some fsp)
        (NEXT: (next < at_most)%ord)

        (POST: gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) rg rg _ _ eqr n1 a
                      (mp_src0,
                       ('(ctx1, fr1, _) <- (HoareCall mn true o fsp fn args ctx0);;
                        Tau (ITree.bind (interp_hCallE_tgt mn stb o (_APC next) (ctx1, fr1)) k_src)))
                      (itr_tgt))
    :
      gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) r rg _ _ eqr n0 a
             (mp_src0, (interp_hCallE_tgt mn stb o (_APC at_most) ctx0) >>= k_src)
             (itr_tgt).
  Proof.
    destruct ctx0. destruct itr_tgt.
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
    | [SIM: gpaco7 _ _ _ _ _ _ _ _ _ ?i0 _ |- gpaco7 _ _ _ _ _ _ _ _ _ ?i1 _] =>
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
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, guarantee ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; gstep; eapply sim_itree_choose_src; [eauto with ord_step|exists name]|contradict name]; cycle 1

  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp _ guarantee ?P) (_, _))) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; gstep; eapply sim_itree_choose_src; [eauto with ord_step|exists name]|contradict name]; cycle 1

   (* TODO: handle interp_hCallE_tgt better and remove this case *)
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp _ (guarantee ?P ))) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; gstep; eapply sim_itree_choose_src; [eauto with ord_step|exists name]|contradict name]; cycle 1; clear name

  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_tgt; gstep; econs; eauto with ord_step; unseal i_tgt
  end
.

Ltac force_r :=
  prep;
  match goal with
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    destruct (classic P) as [name|name]; [ired_both; gstep; eapply sim_itree_take_tgt; [eauto with ord_step|exists name]|contradict name]; cycle 1

  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_src; gstep; econs; eauto with ord_step; unseal i_src
  end
.

Ltac _step :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, triggerUB >>= _) (_, _)) ] =>
    unfold triggerUB; ired_l; _step; done
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; force_l; ss; fail]
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_both; gstep; eapply sim_itree_take_src; [eapply OrdArith.lt_from_nat; apply Nat.lt_succ_diag_r|]; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, triggerNB >>= _) (_, _)) ] =>
    unfold triggerNB; ired_r; _step; done
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; force_r; ss; fail]
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_both; gstep; eapply sim_itree_choose_tgt; [eapply OrdArith.lt_from_nat; apply Nat.lt_succ_diag_r|]; intro name



  | _ => (*** default ***)
    gstep; eapply safe_sim_sim; econs; try (eapply OrdArith.lt_from_nat; apply Nat.lt_succ_diag_r); i
  end;
  match goal with
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.
Ltac steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) unfold alist_add; simpl; des_ifs_safe).

Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 tgt1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco7 (_sim_itree wf _) _ _ _ _ _ _ _ n ((src0, src1), src2) ((tgt0, tgt1), tgt2))
      (at level 60,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' tgt1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Section TEST.
  Context `{Σ: GRA.t} `{ns: gnames}.
  Let wf := (mk_wf (fun (_ : unit) (_ _ : Any.t) => bi_pure True)).
  Let le := fun (_ _: unit) => True.
  Variable (srcs0 tgts0: Any.t).

  Goal gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) bot7 bot7 Any.t Any.t (fun _ _ => eq) 100 tt
       (srcs0, triggerUB >>= idK) (tgts0, triggerUB >>= idK).
    i.
    steps.
  Qed.

  Goal gpaco7 (_sim_itree wf le) (cpn7 (_sim_itree wf le)) bot7 bot7 Any.t Any.t (fun _ _ => eq) 100 tt
       (srcs0, triggerNB >>= idK) (tgts0, triggerNB >>= idK).
    i.
    steps.
  Qed.

End TEST.

Require Import TODOYJ.

Ltac astep_full _fn _args _next _n1 :=
  eapply (@APC_step_clo _ _ _fn _args _next _n1);
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; lia)]))|
   (try by ((try stb_tac); refl))|
   (eapply OrdArith.lt_from_nat; lia)|
  ].

Ltac astep _fn _args :=
  eapply (@APC_step_clo _ _ _fn _args);
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
   (try by ((try stb_tac); refl))|
   (eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r)|
  ].

Ltac acatch :=
  match goal with
  | [ |- (gpaco7 (_sim_itree _ _) _ _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn ?args) >>= _)) ] =>
    astep fn args
  end.

Ltac astop :=
  eapply APC_stop_clo;
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|].

Ltac astart _at_most :=
  eapply (@APC_start_clo _ _ _at_most);
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
  let mn := fresh "mn" in
  let varg := fresh "varg" in
  let EQ := fresh "EQ" in
  let w := fresh "w" in
  let mrp_src := fresh "mrp_src" in
  let mp_tgt := fresh "mp_tgt" in
  let WF := fresh "WF" in
  split; ss; intros varg_src [mn varg] EQ w mrp_src mp_tgt WF;
  (try subst varg_src); exists 100; cbn;
  ginit;
  try (unfold fun_to_tgt, cfun; rewrite HoareFun_parse); simpl.

Ltac harg :=
  let PRE := constr:("PRE") in
  let INV := constr:("INV") in
  eapply (@harg_clo _ _ _ PRE INV);
  [eassumption
  |
  ]; i.

Tactic Notation "hret" uconstr(a) :=
  eapply (@hret_clo _ _ _ a); unshelve_goal;
  [eauto with ord_step
  |eassumption
  |
  |start_ipm_proof
  |try by (i; (try unfold lift_rel); esplits; et)
  ].

Tactic Notation "hcall" uconstr(o) uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let Hns := select_ihyps Hns in
  eapply (@hcall_clo _ _ Hns POST INV o _ x _ a);
  unshelve_goal;
  [eassumption
  |start_ipm_proof
  |eauto with ord_step
  |
  |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H)
  ].

Tactic Notation "hcall_weaken" uconstr(fsp) uconstr(o) uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let Hns := select_ihyps Hns in
  eapply (@hcall_clo_weaken _ _ Hns POST INV _ _ fsp o _ x _ a);
  unshelve_goal;
  [
  |eassumption
  |start_ipm_proof
  |eauto with ord_step
  |
  |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H)
  ].

Global Opaque _APC APC interp interp_hCallE_tgt.

Global Opaque HoareFun HoareFunArg HoareFunRet HoareCall.

Definition __hide_mark A (a : A) : A := a.
Lemma intro_hide_mark: forall A (a: A), a = __hide_mark a. refl. Qed.

Ltac hide_k :=
  match goal with
  | [ |- (gpaco7 _ _ _ _ _ _ _ _ _ (_, ?isrc >>= ?ksrc) (_, ?itgt >>= ?ktgt)) ] =>
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
