Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef SimModSem.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
From Ordinal Require Export Ordinal Arithmetic.
Require Import Red.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.

#[export] Hint Resolve sim_itree_mon: paco.
#[export] Hint Resolve cpn6_wcompat: paco.

Create HintDb ord_step.
#[export] Hint Resolve Nat.lt_succ_diag_r OrdArith.lt_from_nat OrdArith.lt_add_r: ord_step.
#[export] Hint Extern 1000 => lia: ord_step.


(* itree reduction *)

Lemma interp_tgt_bind `{Σ: GRA.t} stb o
      (R S R_src: Type)
      (s : itree (hCallE +' pE +' eventE) R) (k : R -> itree (hCallE +' pE +' eventE) S) (h : S -> itree _ R_src)
  :
    (interp_hCallE_tgt (E:=pE +' eventE) stb o (s >>= k) >>= h)
    =
    ((interp_hCallE_tgt (E:=pE +' eventE) stb o s) >>= (fun r => interp_hCallE_tgt stb o (k r) >>= h)).
Proof.
  unfold interp_hCallE_tgt in *. grind.
Qed.

Lemma interp_tgt_tau `{Σ: GRA.t} stb o
      (U R_src: Type)
      (t : itree _ _) (k : U -> itree _ R_src)
  :
    (interp_hCallE_tgt (E:=pE +' eventE) stb o (Tau t) >>= k)
    =
    (Tau (interp_hCallE_tgt (E:=pE +' eventE) stb o t >>= k)).
Proof.
  unfold interp_hCallE_tgt in *. grind.
Qed.

Lemma interp_tgt_ret `{Σ: GRA.t} stb o
      (U R_src: Type)
      t (k : U -> itree Es R_src)
  :
    ((interp_hCallE_tgt (E:=pE +' eventE) stb o (Ret t)) >>= k)
    =
    k t.
Proof.
  unfold interp_hCallE_tgt in *. grind.
Qed.

Lemma interp_tgt_triggerp `{Σ: GRA.t} stb o
      (R R_src: Type)
      (h : R -> itree _ R_src) (i: pE R)
  :
    (interp_hCallE_tgt (E:=pE +' eventE) stb o (trigger i) >>= h)
    =
    (trigger i >>= (fun r => Tau (h r))).
Proof.
  unfold interp_hCallE_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_tgt_triggere `{Σ: GRA.t} stb o
      (R R_src: Type)
      (h : R -> itree _ R_src) (i: eventE R)
  :
    (interp_hCallE_tgt (E:=pE +' eventE) stb o (trigger i) >>= h)
    =
    (trigger i >>= (fun r => Tau (h r))).
Proof.
  unfold interp_hCallE_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_tgt_hcall `{Σ: GRA.t} stb o
      (R R_src: Type)
      (h : R -> itree _ R_src) (i: hCallE R)
  :
    (interp_hCallE_tgt (E:=pE +' eventE) stb o (trigger i) >>= h)
    =
    ((handle_hCallE_tgt stb o i) >>= (fun r => Tau (h r))).
Proof.
  unfold interp_hCallE_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_tgt_triggerUB `{Σ: GRA.t} stb o
      (R R_src: Type)
      (h : R -> itree _ R_src)
  :
    (interp_hCallE_tgt (E:=pE +' eventE) stb o (triggerUB)) >>= h
    =
    triggerUB >>= (fun x => Ret x).
Proof.
  unfold interp_hCallE_tgt, triggerUB in *. etrans.
  { eapply interp_tgt_bind. } etrans.
  { eapply interp_tgt_triggere. }
  grind.
Qed.

Lemma interp_tgt_triggerNB `{Σ: GRA.t} stb o
      (R R_src: Type)
      (h : R -> itree _ R_src)
  :
    (interp_hCallE_tgt (E:=pE +' eventE) stb o (triggerNB)) >>= h
    =
    triggerNB >>= (fun x => Ret x).
Proof.
  unfold interp_hCallE_tgt, triggerNB in *. etrans.
  { eapply interp_tgt_bind. } etrans.
  { eapply interp_tgt_triggere. }
  grind.
Qed.

Lemma interp_tgt_unwrapU `{Σ: GRA.t} stb o
      (R R_src: Type)
      (h : R -> itree _ R_src) (i: option R)
  :
    (interp_hCallE_tgt (E:=pE +' eventE) stb o (@unwrapU (hCallE +' pE +' eventE) _ _ i) >>= h)
    =
    (unwrapU i >>= h).
Proof.
  unfold interp_hCallE_tgt, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_tgt_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_tgt_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_tgt_unwrapN `{Σ: GRA.t} stb o
      (R R_src: Type)
      (h : R -> itree _ R_src) (i: option R)
  :
    (interp_hCallE_tgt (E:=pE +' eventE) stb o (@unwrapN (hCallE +' pE +' eventE) _ _ i) >>= h)
    =
    (unwrapN i >>= h).
Proof.
  unfold interp_hCallE_tgt, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_tgt_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_tgt_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_tgt_assume `{Σ: GRA.t} stb o
      (R_src: Type)
      (h : _ -> itree _ R_src) P
  :
    (interp_hCallE_tgt (E:=pE +' eventE) stb o (assume P) >>= h)
    =
    (assume P >>= (fun r => Tau (h r))).
Proof.
  unfold assume. etrans.
  { eapply interp_tgt_bind. } etrans.
  { eapply interp_tgt_triggere. }
  grind. eapply interp_tgt_ret.
Qed.

Lemma interp_tgt_guarantee `{Σ: GRA.t} stb o
      (R_src: Type)
      (h : _ -> itree _ R_src) P
  :
    (interp_hCallE_tgt (E:=pE +' eventE) stb o (guarantee P) >>= h)
    =
    (guarantee P >>= (fun r => Tau (h r))).
Proof.
  unfold guarantee. etrans.
  { eapply interp_tgt_bind. } etrans.
  { eapply interp_tgt_triggere. }
  grind. eapply interp_tgt_ret.
Qed.

Ltac interp_red := rewrite interp_vis ||
                           rewrite interp_ret ||
                           rewrite interp_tau ||
                           rewrite interp_trigger ||
                           rewrite interp_bind.

Ltac interp_mrec_red := rewrite interp_mrec_hit ||
                                rewrite interp_mrec_miss ||
                                rewrite interp_mrec_bind ||
                                rewrite interp_mrec_tau ||
                                rewrite interp_mrec_ret.

Ltac interp_state_red := rewrite interp_state_trigger ||
                                 rewrite interp_state_bind ||
                                 rewrite interp_state_tau ||
                                 rewrite interp_state_ret.

Ltac _red_itree f :=
  match goal with
  | [ |- ITree.bind' _ ?itr = _] =>
    match itr with
    | ITree.bind' _ _ =>
      instantiate (f:=_continue); apply bind_bind; fail
    | Tau _ =>
      instantiate (f:=_break); apply bind_tau; fail
    | Ret _ =>
      instantiate (f:=_continue); apply bind_ret_l; fail
    | _ =>
      fail
    end
  | [ |- trigger _ = _] =>
    instantiate (f:=_break); apply bind_ret_r_rev; fail
  | _ => fail
  end.

Ltac _red_interp_tgt f :=
  match goal with
  | [ |- ITree.bind' _ (interp_hCallE_tgt _ _ ?itr) = _ ] =>
    match itr with
    | ITree.bind' _ _ =>
      instantiate (f:=_continue); eapply interp_tgt_bind; fail
    | Tau _ =>
      instantiate (f:=_break); apply interp_tgt_tau; fail
    | Ret _ =>
      instantiate (f:=_continue); apply interp_tgt_ret; fail
    | trigger ?e =>
      instantiate (f:=_break);
      match (type of e) with
      | context[hCallE] => apply interp_tgt_hcall
      | context[eventE] => apply interp_tgt_triggere
      | context[pE] => apply interp_tgt_triggerp
      | _ => fail 2
      end
    | triggerUB =>
      instantiate (f:=_break); apply interp_tgt_triggerUB; fail
    | triggerNB =>
      instantiate (f:=_break); apply interp_tgt_triggerNB; fail
    | unwrapU _ =>
      instantiate (f:=_break); apply interp_tgt_unwrapU; fail
    | unwrapN _ =>
      instantiate (f:=_break); apply interp_tgt_unwrapN; fail
    | assume _ =>
      instantiate (f:=_break); apply interp_tgt_assume; fail
    | guarantee _ =>
      instantiate (f:=_break); apply interp_tgt_guarantee; fail
    | _ =>
      fail
    end
  | [ |- interp_hCallE_tgt _ _ _ = _] =>
    instantiate (f:=_continue); apply bind_ret_r_rev; fail
  | _ => fail
  end.

Ltac _red_lsim f :=
  _red_interp_tgt f || _red_itree f || fail.

Ltac ired_l := try (prw _red_lsim 2 1 0).
Ltac ired_r := try (prw _red_lsim 1 1 0).

Ltac ired_both := ired_l; ired_r.


(* any, alist things *)

Ltac anytac := (try rewrite ! Any.upcast_downcast in *); clarify; apply_all_once Any.upcast_inj; des; clarify; clear_tac.

Ltac asimpl := try (unfold alist_add, alist_remove in *); ss.


(* Hoare Parse *)

Section HOARE.
  Let Any_tgt := Any.t.
  Notation Es' := (hCallE +' pE +' eventE).
  Context `{Σ: GRA.t}.
  Variable stb: list (gname * fspec).

  Definition HoareFunArg
             {X Y: Type}
             (P: X -> Y -> Any_tgt -> ord -> Σ -> Prop): Any_tgt -> itree Es (X * Y * ord) := fun varg_tgt =>
    varg_src <- trigger (Take Y);;
    x <- trigger (Take X);;
    rarg <- trigger (Take Σ);; forge rarg;; (*** virtual resource passing ***)
    (checkWf);;
    ord_cur <- trigger (Take _);;
    assume(P x varg_src varg_tgt ord_cur rarg);; (*** precondition ***)
    Ret (x, varg_src, ord_cur)
  .

  Definition HoareFunRet
             {X Z: Type}
             (Q: X -> Z -> Any_tgt -> Σ -> Prop): X -> Z -> itree Es Any_tgt := fun x vret_src =>
    vret_tgt <- trigger (Choose Any_tgt);;
    '(mret, fret) <- trigger (Choose _);; put mret fret;; (*** updating resources in an abstract way ***)
    rret <- trigger (Choose Σ);; guarantee(Q x vret_src vret_tgt rret);; (*** postcondition ***)
    (discard rret);; (*** virtual resource passing ***)

    Ret vret_tgt (*** return ***)
  .

  Lemma HoareFun_parse
        {X Y Z: Type}
        (P: X -> Y -> Any_tgt -> ord -> Σ -> Prop)
        (Q: X -> Z -> Any_tgt -> Σ -> Prop)
        (body: Y -> itree Es' Z)
        (varg_tgt: Any_tgt)
    :
      HoareFun stb P Q body varg_tgt =
      '(x, varg_src, ord_cur) <- HoareFunArg P varg_tgt;;
      vret_src <- match ord_cur with
                  | ord_pure n => (interp_hCallE_tgt stb ord_cur APC);; trigger (Choose _)
                  | _ => (interp_hCallE_tgt stb ord_cur (body varg_src))
                  end;;
      HoareFunRet Q x vret_src.
  Proof.
    unfold HoareFun, HoareFunArg, HoareFunRet, body_to_tgt. grind.
  Qed.
End HOARE.


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

  Lemma hcall_clo_ord_weaken (o_new: Ord.t) Y Z (ftsp1: ftspec Y Z) (x: ftsp1.(X)) (o: ord)
        (mr_src1 fr_src1 rarg_src: Σ)
        r rg (n: nat) mr_src0 mp_src0 fr_src0
        (ftsp0: ftspec Y Z)
        mrs_tgt frs_tgt k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)

        (WEAKER: ftspec_weaker ftsp1 ftsp0)
        (UPDATABLE: URA.updatable (URA.add mr_src0 fr_src0) (URA.add mr_src1 (URA.add rarg_src fr_src1)))
        (FUEL: (15 < n)%ord)
        (PRE: ftsp1.(precond) x varg_src varg_tgt o rarg_src)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))
        (WF: wf ((mr_src1, mp_src0), mrs_tgt))
        (POST: forall (vret_tgt : Any.t) (mrs_src1 mrs_tgt1 : (Σ * Any.t))
                      (rret: Σ) (vret_src: Z)
                      (WF: wf (mrs_src1, mrs_tgt1)),
            exists (mr_src2: Σ) (mp_src2: Any.t),
              (<<LOOKUP: mrs_src1 = (mr_src2, mp_src2)>>) /\
              forall (VALID: URA.wf (URA.add mr_src2 (URA.add fr_src1 rret)))
                     (POST: ftsp1.(postcond) x vret_src vret_tgt rret),
                gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ (fun _ _ => @eq Any.t) o_new
                       (mrs_src1, URA.add fr_src1 rret, k_src vret_src) (mrs_tgt1, frs_tgt, k_tgt vret_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ (fun _ _ => @eq Any.t) n
             (mr_src0, mp_src0, fr_src0, (HoareCall tbr ord_cur (mk_fspec ftsp0) fn varg_src) >>= k_src)
             (mrs_tgt, frs_tgt, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    unfold HoareCall, put, discard, forge, checkWf, assume, guarantee.
    ired_both. gstep. econs; [eauto with ord_step|].
    exists (mr_src1, URA.add rarg_src fr_src1).
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists rarg_src.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists fr_src1.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    hexploit (WEAKER x). i. des.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists o.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto. des.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). i. exists (o_new + 8)%ord.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.
    hexploit (POST vret mrs_src1 mrs_tgt1 x0 x1 WF0). i. des. subst.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.
    ired_both; gstep; econs.
    { instantiate (1:=o_new). eapply Ord.eq_lt_lt.
      { symmetry. eapply OrdArith.add_O_r. }
      { eapply OrdArith.lt_add_r. rewrite Ord.from_nat_S. eapply Ord.S_pos. }
    }
    i.
    repeat spc H0.
    ired_both; ss. et.
  Qed.

  Lemma hcall_clo_weaken Y Z (ftsp1: ftspec Y Z) (x: ftsp1.(X)) (o: ord)
        (mr_src1 fr_src1 rarg_src: Σ)
        r rg (n: nat) mr_src0 mp_src0 fr_src0
        (ftsp0: ftspec Y Z)
        mrs_tgt frs_tgt k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)

        (WEAKER: ftspec_weaker ftsp1 ftsp0)
        (UPDATABLE: URA.updatable (URA.add mr_src0 fr_src0) (URA.add mr_src1 (URA.add rarg_src fr_src1)))
        (FUEL: (15 < n)%ord)
        (PRE: ftsp1.(precond) x varg_src varg_tgt o rarg_src)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))
        (WF: wf ((mr_src1, mp_src0), mrs_tgt))
        (POST: forall (vret_tgt : Any.t) (mrs_src1 mrs_tgt1 : (Σ * Any.t))
                      (rret: Σ) (vret_src: Z)
                      (WF: wf (mrs_src1, mrs_tgt1)),
            exists (mr_src2: Σ) (mp_src2: Any.t),
              (<<LOOKUP: mrs_src1 = (mr_src2, mp_src2)>>) /\
              forall (VALID: URA.wf (URA.add mr_src2 (URA.add fr_src1 rret)))
                     (POST: ftsp1.(postcond) x vret_src vret_tgt rret),
                gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ (fun _ _ => @eq Any.t) 100
                       (mrs_src1, URA.add fr_src1 rret, k_src vret_src) (mrs_tgt1, frs_tgt, k_tgt vret_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ (fun _ _ => @eq Any.t) n
             (mr_src0, mp_src0, fr_src0, (HoareCall tbr ord_cur (mk_fspec ftsp0) fn varg_src) >>= k_src)
             (mrs_tgt, frs_tgt, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    eapply (@hcall_clo_ord_weaken 100); eauto.
  Qed.

  Lemma hcall_clo
        (mr_src1 fr_src1 rarg_src: Σ)
        (o: ord) X (x: X)
        r rg (n: nat) mr_src0 mp_src0 fr_src0 Y Z
        (P: X -> Y -> Any.t -> ord -> Σ -> Prop)
        (Q: X -> Z -> Any.t -> Σ -> Prop)
        mrs_tgt frs_tgt k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)

        (UPDATABLE: URA.updatable (URA.add mr_src0 fr_src0) (URA.add mr_src1 (URA.add rarg_src fr_src1)))
        (FUEL: (15 < n)%ord)
        (PRE: P x varg_src varg_tgt o rarg_src)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))
        (WF: wf ((mr_src1, mp_src0), mrs_tgt))
        (POST: forall (vret_tgt : Any.t) (mrs_src1 mrs_tgt1 : (Σ * Any.t))
                      (rret: Σ) (vret_src: Z)
                      (WF: wf (mrs_src1, mrs_tgt1)),
            exists (mr_src2: Σ) (mp_src2: Any.t),
              (<<LOOKUP: mrs_src1 = (mr_src2, mp_src2)>>) /\
              forall (VALID: URA.wf (URA.add mr_src2 (URA.add fr_src1 rret)))
                     (POST: Q x vret_src vret_tgt rret),
                gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ (fun _ _ => @eq Any.t) 100
                       (mrs_src1, URA.add fr_src1 rret, k_src vret_src) (mrs_tgt1, frs_tgt, k_tgt vret_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ (fun _ _ => @eq Any.t) n
             (mr_src0, mp_src0, fr_src0, (HoareCall tbr ord_cur (mk P Q) fn varg_src) >>= k_src)
             (mrs_tgt, frs_tgt, trigger (Call fn varg_tgt) >>= k_tgt).
  Proof.
    eapply hcall_clo_weaken; eauto.
    { refl. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma harg_clo
        r rg mr_src0 mp_src0 fr_src0
        X Y (P: X -> Y -> Any.t -> ord -> Σ -> Prop) varg_tgt
        mrs_tgt frs_tgt f_tgt k_src
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (ARG:
           forall x varg_src rarg_src ord_cur
                  (VALID: URA.wf (URA.add mr_src0 (URA.add fr_src0 rarg_src)))
                  (PRE: P x varg_src varg_tgt ord_cur rarg_src),
             gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ (fun _ _ => @eq Any.t) 90
                    (mr_src0, mp_src0, URA.add fr_src0 rarg_src, k_src (x, varg_src, ord_cur))
                    (mrs_tgt, frs_tgt, f_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ (fun _ _ => @eq Any.t) 100
              (mr_src0, mp_src0, fr_src0, (HoareFunArg P varg_tgt >>= k_src))
              (mrs_tgt, frs_tgt, f_tgt)
  .
  Proof.
    unfold HoareFunArg, put, discard, forge, checkWf, assume, guarantee.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro varg_src.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro x.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro rarg_src.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro VALID.
    repeat (ired_both; gstep; econs; eauto with ord_step). intro ord_cur.
    repeat (ired_both; gstep; econs; eauto with ord_step). i.
    ired_both. eauto.
  Qed.

  Lemma hret_clo (mr_src1 rret_src: Σ)
        r rg n mr_src0 mp_src0 fr_src0
        X Z (Q: X -> Z -> Any.t -> Σ -> Prop)
        x vret_src vret_tgt
        mrs_tgt frs_tgt
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (FUEL: (14 < n)%ord)
        (UPDATABLE: URA.updatable (URA.add mr_src0 fr_src0) (URA.add mr_src1 rret_src))
        (POST: Q x vret_src vret_tgt rret_src)
        (WF: wf ((mr_src1, mp_src0), mrs_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ (fun _ _ => @eq Any.t) n
             (mr_src0, mp_src0, fr_src0, (HoareFunRet Q x vret_src))
             ((mrs_tgt, frs_tgt), (Ret vret_tgt))
  .
  Proof.
    unfold HoareFunRet, put, discard, forge, checkWf, assume, guarantee.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists vret_tgt.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists (mr_src1, rret_src).
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). eexists rret_src.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step). exists ε.
    repeat (ired_both; gstep; econs; eauto with ord_step). unshelve esplits; eauto.
    { rewrite URA.unit_id; ss. }
    repeat (ired_both; gstep; econs; eauto with ord_step).
  Qed.

  Lemma APC_step_clo
        (fn: gname) X (args: X) (next: Ord.t) (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        stb itr_tgt

        (FUEL: (n1 + 7 < n0)%ord)
        (fsp: fspec)
        (FIND: find (fun '(_fn, _) => dec fn _fn) stb = Some (fn, fsp))
        (EQ: X = fsp.(AA))
        (NEXT: (next < at_most)%ord)

        (POST: forall args' (EQ: args' ~= args),
            gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ (fun _ _ => @eq Any.t) n1
                    (mr_src0, mp_src0, fr_src0,
                     (HoareCall true o fsp fn args');; Tau (ITree.bind (interp_hCallE_tgt stb o (_APC next)) k_src))
                   ((mrs_tgt, frs_tgt),
                    itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ (fun _ _ => @eq Any.t) n0
              (mr_src0, mp_src0, fr_src0, (interp_hCallE_tgt stb o (_APC at_most)) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APC. ired_l. gstep. eapply sim_itree_choose_src.
    { eapply FUEL. }
    exists false. gstep. eapply sim_itree_tau_src.
    { eapply OrdArith.lt_add_r. eauto with ord_step. }
    ired_l. gstep. eapply sim_itree_choose_src.
    { eapply OrdArith.lt_add_r. eauto with ord_step. }
    exists next. gstep. eapply sim_itree_tau_src.
    { eapply OrdArith.lt_add_r. eauto with ord_step. }
    ired_l. unfold guarantee. ired_l. gstep. eapply sim_itree_choose_src.
    { eapply OrdArith.lt_add_r. eauto with ord_step. }
    split.
    { auto. }
    ired_l. gstep. eapply sim_itree_tau_src.
    { eapply OrdArith.lt_add_r. eauto with ord_step. }
    ired_l. gstep. eapply sim_itree_choose_src.
    { eapply OrdArith.lt_add_r. eauto with ord_step. }
    exists (fn, args↑).
    ired_l. gstep. eapply sim_itree_tau_src.
    { eapply OrdArith.add_lt_l. rewrite Ord.from_nat_S. eapply Ord.S_pos. }
    ired_l. ss. rewrite FIND. ss. subst. ired_l.
    rewrite Any.upcast_downcast. ss. ired_l.
    exploit (POST args); ss. intros SIM.
    match goal with
    | [SIM: gpaco6 _ _ _ _ _ _ _ _ ?i0 _ |- gpaco6 _ _ _ _ _ _ _ _ ?i1 _] =>
      replace i1 with i0; auto
    end.
    f_equal. grind.
  Qed.

  Lemma APC_stop_clo
        (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        stb itr_tgt

        (FUEL: (n1 + 1 < n0)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ (fun _ _ => @eq Any.t) n1
                      (mr_src0, mp_src0, fr_src0, k_src ())
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ (fun _ _ => @eq Any.t) n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (_APC at_most)) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APC. ired_l. gstep. eapply sim_itree_choose_src.
    { eapply FUEL. }
    exists true. gstep. eapply sim_itree_tau_src.
    { eapply OrdArith.add_lt_l. rewrite Ord.from_nat_S. eapply Ord.S_pos. }
    ired_both. auto.
  Qed.

  Lemma APC_start_clo
        (at_most: Ord.t) (n1: Ord.t)
        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        stb itr_tgt

        (ATMOST: (at_most < kappa)%ord)
        (FUEL: (n1 + 3 < n0)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ (fun _ _ => @eq Any.t) n1
                       (mr_src0, mp_src0, fr_src0,
                       (interp_hCallE_tgt stb o (_APC at_most))>>= k_src)
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ (fun _ _ => @eq Any.t) n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o APC) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    unfold APC. ired_l. gstep. eapply sim_itree_choose_src.
    { eapply FUEL. }
    exists at_most. steps.
    { eauto with ord_step. }
    { unfold guarantee. ired_both. gstep. econs; eauto with ord_step. esplits; eauto.
      ired_both. gstep. econs.
      { instantiate (1:=n1). eapply OrdArith.add_lt_l. rewrite Ord.from_nat_S. eapply Ord.S_pos. }
      ired_both. ss. }
  Qed.

End HLEMMAS.


(* main tactics *)

Ltac init :=
  split; ss; ii; clarify; rename y into varg; eexists 100%nat; ss; des; clarify;
  ginit; asimpl;
  try (unfold fun_to_tgt, cfun; rewrite HoareFun_parse); ss.

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

Require Import TODOYJ Logic YPM.

Ltac harg_tac :=
  _harg_tac;
  match goal with
  | [H: URA.wf ?cur |- _] =>
    let name := fresh "GWF" in
    assert(name: __gwf_mark__ cur cur) by (split; [refl|exact H]); clear H
  end.

Ltac hcall_tac x o MR_SRC1 FR_SRC1 RARG_SRC :=
  let mr_src1 := r_gather MR_SRC1 in
  let fr_src1 := r_gather FR_SRC1 in
  let rarg_src := r_gather RARG_SRC in
  (* let tac0 := etrans; [on_gwf ltac:(fun GWF => apply GWF)|eapply URA.extends_updatable; r_equalize; r_solve] in *)
  (* let tac0 := idtac in *)
  let tac0 := etrans; [etrans; [|on_gwf ltac:(fun GWF => apply GWF)]|]; eapply URA.extends_updatable; r_equalize; r_solve; fail in
  let tac1 := (on_gwf ltac:(fun H => clear H);
               let WF := fresh "WF" in
               let tmp := fresh "_tmp_" in
               let GWF := fresh "GWF" in
               intros ? ? ? ? ? WF; cbn in WF; desH WF; subst;
               esplits; ss; et; intros tmp ?; assert(GWF: ☀) by (split; [refl|exact tmp]); clear tmp; iRefresh; iClears') in
  prep;
  match x with
  | ltac_wild =>
    match o with
    | ltac_wild => eapply (@hcall_clo _ mr_src1 fr_src1 rarg_src); [|tac0|eapply OrdArith.lt_from_nat; lia|..|tac1]
    | _ => eapply (@hcall_clo _ mr_src1 fr_src1 rarg_src o); [|tac0|eapply OrdArith.lt_from_nat; lia|..|tac1]
    end
  | _ => eapply (@hcall_clo _ mr_src1 fr_src1 rarg_src o _ x); [tac0|eapply OrdArith.lt_from_nat; lia|..|tac1]
  end
.

Ltac hret_tac MR_SRC RT_SRC :=
  let mr_src1 := r_gather MR_SRC in
  let fr_src1 := r_gather RT_SRC in
  let tac0 := etrans; [etrans; [|on_gwf ltac:(fun GWF => apply GWF)]|]; eapply URA.extends_updatable; r_equalize; r_solve; fail in
  _hret_tac mr_src1 fr_src1; [tac0| |]
.

Ltac astep_full _fn _args _next _n1 :=
  eapply (@APC_step_clo _ _fn _ _args _next _n1);
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; lia)]))|
   (try by (stb_tac; refl))|
   (try refl)|
   (eapply OrdArith.lt_from_nat; lia)|
   (let args := fresh "args" in
    let EQ := fresh "EQ" in
    intros args EQ; subst args)].

Ltac astep _fn _args :=
  eapply (@APC_step_clo _ _fn _ _args);
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
   (try by (stb_tac; refl))|
   (try refl)|
   (eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r)|
   (let args := fresh "args" in
    let EQ := fresh "EQ" in
    intros args EQ; subst args)].

Ltac astop :=
  eapply APC_stop_clo;
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|].

Ltac astart _at_most :=
  eapply (@APC_start_clo _ _at_most);
  [eauto with ord_kappa|
   (try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
  ]
.

Ltac acall_tac A0 A1 A2 A3 A4 :=
  match goal with
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn (Any.upcast ?args)) >>= _)) ] =>
    astep fn args; hcall_tac A0 A1 A2 A3 A4
  end.

Global Opaque _APC APC interp interp_hCallE_tgt.
