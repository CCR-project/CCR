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

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.

Hint Resolve sim_itree_mon: paco.
Hint Resolve cpn6_wcompat: paco.

Ltac anytac := (try rewrite ! Any.upcast_downcast in *); clarify; apply_all_once Any.upcast_inj; des; clarify; clear_tac.

Ltac asimpl := try (unfold alist_add, alist_remove in *); ss.


Section HOARE.
  Let Any_tgt := Any.t.
  Notation Es' := (hCallE +' pE +' eventE).
  Context `{Σ: GRA.t}.
  Variable stb: list (gname * fspec).

  Definition HoareFunArg
             (mn: mname)
             {X Y: Type}
             (P: X -> Y -> Any_tgt -> ord -> Σ -> Prop): Any_tgt -> itree Es (X * Y * ord) := fun varg_tgt =>
    varg_src <- trigger (Take Y);;
    x <- trigger (Take X);;
    rarg <- trigger (Take Σ);; forge rarg;; (*** virtual resource passing ***)
    (checkWf mn);;
    ord_cur <- trigger (Take _);;
    assume(P x varg_src varg_tgt ord_cur rarg);; (*** precondition ***)
    Ret (x, varg_src, ord_cur)
  .

  Definition HoareFunRet
             (mn: mname)
             {X Z: Type}
             (Q: X -> Z -> Any_tgt -> Σ -> Prop): X -> Z -> itree Es Any_tgt := fun x vret_src =>
    vret_tgt <- trigger (Choose Any_tgt);;
    '(mret, fret) <- trigger (Choose _);; put mn mret fret;; (*** updating resources in an abstract way ***)
    rret <- trigger (Choose Σ);; guarantee(Q x vret_src vret_tgt rret);; (*** postcondition ***)
    (discard rret);; (*** virtual resource passing ***)

    Ret vret_tgt (*** return ***)
  .

  Lemma HoareFun_parse
        (mn: mname)
        {X Y Z: Type}
        (P: X -> Y -> Any_tgt -> ord -> Σ -> Prop)
        (Q: X -> Z -> Any_tgt -> Σ -> Prop)
        (body: Y -> itree Es' Z)
        (varg_tgt: Any_tgt)
    :
      HoareFun stb mn P Q body varg_tgt =
      '(x, varg_src, ord_cur) <- HoareFunArg mn P varg_tgt;;
      vret_src <- match ord_cur with
                  | ord_pure n => (interp_hCallE_tgt stb mn ord_cur APC);; trigger (Choose _)
                  | _ => (interp_hCallE_tgt stb mn ord_cur (body varg_src))
                  end;;
      HoareFunRet mn Q x vret_src.
  Proof.
    unfold HoareFun, HoareFunArg, HoareFunRet, body_to_tgt.
    ired. repeat f_equal.
    extensionality y. ired. repeat f_equal.
    extensionality x. ired. repeat f_equal.
    extensionality rarg. ired. repeat f_equal.
    extensionality u0. ired. repeat f_equal.
    extensionality u1. ired. repeat f_equal.
    extensionality ord_cur. ired. repeat f_equal.
  Qed.
End HOARE.


Section SIM.

  Context `{Σ: GRA.t}.

  Let st_local: Type := ((alist mname (Σ * Any.t)) * Σ).
  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  Variable wf: W -> Prop.


  Variant _safe_sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), nat -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : nat -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | safe_sim_itree_ret
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      (WF: wf (mrs_src0, mrs_tgt0))
      v_src v_tgt
      (RET: RR (mrs_src0, fr_src0) (mrs_tgt0, fr_tgt0) v_src v_tgt)
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), (Ret v_src)) ((mrs_tgt0, fr_tgt0), (Ret v_tgt))
  | safe_sim_itree_tau
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (K: sim_itree _ _ RR i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 (st_src0, tau;; i_src) (st_tgt0, tau;; i_tgt)
  | safe_sim_itree_call
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      fn varg k_src k_tgt
      (WF: wf (mrs_src0, mrs_tgt0))
      (K: forall vret mrs_src1 mrs_tgt1 (WF: wf (mrs_src1, mrs_tgt1)),
          exists i1, sim_itree _ _ RR i1 ((mrs_src1, fr_src0), k_src vret) ((mrs_tgt1, fr_tgt0), k_tgt vret))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Call fn varg) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Call fn varg) >>= k_tgt)
  | safe_sim_itree_syscall
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      fn varg k_src k_tgt
      (K: forall vret,
          exists i1, sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src vret) ((mrs_tgt0, fr_tgt0), k_tgt vret))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Syscall fn varg) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Syscall fn varg) >>= k_tgt)
  (*** TODO: sim_syscall is nontrivial; it should accept "injected" memory... ***)
  (*** TODO: simplify the model: Syscall: list val -> val ***)

  | safe_sim_itree_tau_src
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: i1 < i0)
      (K: sim_itree _ _ RR i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | safe_sim_itree_take_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X k_src i_tgt
      (ORD: i1 < i0)
      (K: forall (x: X), sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src x) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Take X) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)

  | safe_sim_itree_pput_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0 mp1 mrs_src1 mp0
      (MR0: Maps.lookup mn mrs_src0 = Some (mr0, mp0))
      (EQ: mrs_src1 = Maps.add mn (mr0, mp1) mrs_src0)
      (K: sim_itree _ _ RR i1 ((mrs_src1, fr_src0), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (PPut mn mp1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | safe_sim_itree_mput_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0 mr1 mrs_src1 mp0
      (MR0: Maps.lookup mn mrs_src0 = Some (mr0, mp0))
      (EQ: mrs_src1 = Maps.add mn (mr1, mp0) mrs_src0)
      (K: sim_itree _ _ RR i1 ((mrs_src1, fr_src0), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (MPut mn mr1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | safe_sim_itree_fput_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      fr_src1
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src1), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (FPut fr_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)

  | safe_sim_itree_pget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0 mp0
      (MR0: Maps.lookup mn mrs_src0 = Some (mr0, mp0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src mp0) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (PGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | safe_sim_itree_mget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0 mp0
      (MR0: Maps.lookup mn mrs_src0 = Some (mr0, mp0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src mr0) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (MGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | safe_sim_itree_fget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src fr_src0) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (FGet) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)

  | safe_sim_itree_tau_tgt
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: i1 < i0)
      (K: sim_itree _ _ RR i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree sim_itree RR i0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | safe_sim_itree_choose_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X i_src k_tgt
      (ORD: i1 < i0)
      (K: forall (x: X), sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt x))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Choose X) >>= k_tgt)

  | safe_sim_itree_pput_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0 mp1 mrs_tgt1 mp0
      (MR0: Maps.lookup mn mrs_tgt0 = Some (mr0, mp0))
      (EQ: mrs_tgt1 = Maps.add mn (mr0, mp1) mrs_tgt0)
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt1, fr_tgt0), k_tgt tt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PPut mn mp1) >>= k_tgt)
  | safe_sim_itree_mput_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0 mr1 mrs_tgt1 mp0
      (MR0: Maps.lookup mn mrs_tgt0 = Some (mr0, mp0))
      (EQ: mrs_tgt1 = Maps.add mn (mr1, mp0) mrs_tgt0)
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt1, fr_tgt0), k_tgt tt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (MPut mn mr1) >>= k_tgt)
  | safe_sim_itree_fput_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      fr_tgt1
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt1), k_tgt tt))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FPut fr_tgt1) >>= k_tgt)

  | safe_sim_itree_pget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0 mp0
      (MR0: Maps.lookup mn mrs_tgt0 = Some (mr0, mp0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt mp0))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PGet mn) >>= k_tgt)
  | safe_sim_itree_mget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0 mp0
      (MR0: Maps.lookup mn mrs_tgt0 = Some (mr0, mp0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt mr0))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (MGet mn) >>= k_tgt)
  | safe_sim_itree_fget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt  fr_tgt0))
    :
      _safe_sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FGet) >>= k_tgt)
  .

  Lemma safe_sim_sim:
    _safe_sim_itree <7= _sim_itree wf.
  Proof.
    i. inv PR; try by (econs; eauto).
  Qed.

End SIM.



Ltac init :=
  split; ss; ii; clarify; rename y into varg; eexists 100%nat; ss; des; clarify;
  ginit; asimpl;
  try (unfold fun_to_tgt, cfun; rewrite HoareFun_parse); ss.

Lemma sim_l_bind_bind `{Σ: GRA.t}
      (R S R_src R_tgt: Type) (RR: _ -> _ -> R_src -> R_tgt -> Prop)
      a b c d e f g
      (s : itree _ R) (k : R -> itree _ S) (h : S -> itree _ _)
      (SIM: gpaco6 (_sim_itree c) d e f _ _ RR g (b, ` r : R <- s;; ` x : _ <- k r;; h x) a)
  :
    gpaco6 (_sim_itree c) d e f _ _ RR g (b, ` x : _ <- (` x : _ <- s;; k x);; h x) a.
Proof.
  rewrite bind_bind. auto.
Qed.

Lemma sim_l_bind_tau `{Σ: GRA.t}
      (U R_src R_tgt: Type) (RR: _ -> _ -> R_src -> R_tgt -> Prop)
      a b c d e f g
      (t : itree _ _) (k : U -> itree _ _)
      (SIM: gpaco6 (_sim_itree c) d e f _ _ RR g (b, Tau (` x : _ <- t;; k x)) a)
  :
    gpaco6 (_sim_itree c) d e f _ _ RR g (b, ` x : _ <- Tau t;; k x) a.
Proof.
  rewrite bind_tau. auto.
Qed.

Lemma sim_l_bind_ret_l `{Σ: GRA.t}
      (R R_src R_tgt: Type) (RR: _ -> _ -> R_src -> R_tgt -> Prop)
      a b c d e f g
      (r : R) (k : R -> itree _ _)
      (SIM: gpaco6 (_sim_itree c) d e f _ _ RR g (b, k r) a)
  :
    gpaco6 (_sim_itree c) d e f _ _ RR g (b, ` x : _ <- Ret r;; k x) a.
Proof.
  rewrite bind_ret_l. auto.
Qed.

Lemma sim_l_trigger_ret_rev `{Σ: GRA.t}
      (R_src R_tgt: Type) (RR: _ -> _ -> R_src -> R_tgt -> Prop)
      a b c d e f g (h: Es R_src)
      (SIM: gpaco6 (_sim_itree c) d e f _ _ RR g (b, ` x: _ <- trigger h;; Ret x) a)
  :
    gpaco6 (_sim_itree c) d e f _ _ RR g (b, trigger h) a.
Proof.
  rewrite bind_ret_r in SIM. auto.
Qed.

Lemma sim_r_bind_bind `{Σ: GRA.t}
      (R S R_src R_tgt: Type) (RR: _ -> _ -> R_src -> R_tgt -> Prop)
      a b c d e f g
      (s : itree _ R) (k : R -> itree _ S) (h : S -> itree _ _)
      (SIM: gpaco6 (_sim_itree c) d e f _ _ RR g a (b, ` r : R <- s;; ` x : _ <- k r;; h x))
  :
    gpaco6 (_sim_itree c) d e f _ _ RR g a (b, ` x : _ <- (` x : _ <- s;; k x);; h x).
Proof.
  rewrite bind_bind. auto.
Qed.

Lemma sim_r_bind_tau `{Σ: GRA.t}
      (U R_src R_tgt: Type) (RR: _ -> _ -> R_src -> R_tgt -> Prop)
      a b c d e f g
      (t : itree _ _) (k : U -> itree _ _)
      (SIM: gpaco6 (_sim_itree c) d e f _ _ RR g a (b, Tau (` x : _ <- t;; k x)))
  :
    gpaco6 (_sim_itree c) d e f _ _ RR g a (b, ` x : _ <- Tau t;; k x).
Proof.
  rewrite bind_tau. auto.
Qed.

Lemma sim_r_bind_ret_l `{Σ: GRA.t}
      (R R_src R_tgt: Type) (RR: _ -> _ -> R_src -> R_tgt -> Prop)
      a b c d e f g
      (r : R) (k : R -> itree _ _)
      (SIM: gpaco6 (_sim_itree c) d e f _ _ RR g a (b, k r))
  :
    gpaco6 (_sim_itree c) d e f _ _ RR g a (b, ` x : _ <- Ret r;; k x).
Proof.
  rewrite bind_ret_l. auto.
Qed.

Lemma sim_r_trigger_ret_rev `{Σ: GRA.t}
      (R_src R_tgt: Type) (RR: _ -> _ -> R_src -> R_tgt -> Prop)
      a b c d e f g (h: Es R_tgt)
      (SIM: gpaco6 (_sim_itree c) d e f _ _ RR g a (b, ` x: _ <- trigger h;; Ret x))
  :
    gpaco6 (_sim_itree c) d e f _ _ RR g a (b, trigger h).
Proof.
  rewrite bind_ret_r in SIM. auto.
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

Ltac ired_l :=
  cbn;
  match goal with
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, ITree.bind' _ (ITree.bind' _ _)) _) ] =>
    apply sim_l_bind_bind; ired_l
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, ITree.bind' _ (Tau _)) _) ] =>
    apply sim_l_bind_tau
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, ITree.bind' _ (Ret _)) _) ] =>
    apply sim_l_bind_ret_l; ired_l
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, trigger _) _) ] =>
    apply sim_l_trigger_ret_rev
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, interp _ _) _) ] =>
    ((interp_red; ired_l) || idtac)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, ITree.bind' _ (interp _ _)) _) ] =>
    ((interp_red; ired_l) || idtac)
  | _ => idtac
  end.

Ltac ired_r :=
  cbn;
  match goal with
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (ITree.bind' _ _))) ] =>
    apply sim_r_bind_bind; ired_r
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (Tau _))) ] =>
    apply sim_r_bind_tau
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (Ret _))) ] =>
    apply sim_r_bind_ret_l
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, trigger _)) ] =>
    apply sim_r_trigger_ret_rev
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, interp _ _)) ] =>
    ((interp_red; ired_r) || idtac)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp _ _))) ] =>
    ((interp_red; ired_r) || idtac)
  | _ => idtac
  end.

Ltac ired_all := ired_l; ired_r.

Ltac prep := ired_all.

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
    destruct (classic P) as [name|name]; [ired_all; gstep; eapply sim_itree_choose_src; [eauto|exists name]|contradict name]; cycle 1

  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_tgt; gstep; econs; eauto; unseal i_tgt
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
    destruct (classic P) as [name|name]; [ired_all; gstep; eapply sim_itree_take_tgt; [eauto|exists name]|contradict name]; cycle 1

  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_src; gstep; econs; eauto; unseal i_src
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
    destruct (ox) eqn:name; [|unfold triggerUB; ired_all; force_l; ss; fail]
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_all; gstep; eapply sim_itree_take_src; [apply Nat.lt_succ_diag_r|]; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_all; force_r; ss; fail]
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_all; gstep; eapply sim_itree_choose_tgt; [apply Nat.lt_succ_diag_r|]; intro name



  | _ => (*** default ***)
    gstep; eapply safe_sim_sim; econs; try apply Nat.lt_succ_diag_r; i
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
    (gpaco6 (_sim_itree wf) _ _ _ _ _ _ n (([(_, src0)], src1), src2) (([(_, tgt0)], tgt1), tgt2))
      (at level 60,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' tgt1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Section HLEMMAS.
  Context `{Σ: GRA.t}.
  Local Opaque GRA.to_URA.

  Lemma hcall_clo
        X (x: X) (o: ord)
        (mr_src1 fr_src1 rarg_src: Σ)
        r rg (n: nat) mr_src0 mp_src0 fr_src0 Y Z
        (P: X -> Y -> Any.t -> ord -> Σ -> Prop)
        (Q: X -> Z -> Any.t -> Σ -> Prop)
        mrs_tgt frs_tgt k_tgt k_src
        mn fn tbr ord_cur varg_src varg_tgt
        (wf: (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)) -> Prop)

        (UPDATABLE: URA.updatable (URA.add mr_src0 fr_src0) (URA.add mr_src1 (URA.add rarg_src fr_src1)))
        (FUEL: n > 15)
        (PRE: P x varg_src varg_tgt o rarg_src)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))
        (WF: wf ([(mn, (mr_src1, mp_src0))], mrs_tgt))
        (POST: forall (vret_tgt : Any.t) (mrs_src1 mrs_tgt1 : alist string (Σ * Any.t))
                      (rret: Σ) (vret_src: Z)
                      (WF: wf (mrs_src1, mrs_tgt1)),
            exists (mr_src2: Σ) (mp_src2: Any.t),
              (<<LOOKUP: lookup mn mrs_src1 = Some (mr_src2, mp_src2)>>) /\
              forall (VALID: URA.wf (URA.add mr_src2 (URA.add fr_src1 rret)))
                     (POST: Q x vret_src vret_tgt rret),
                gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ (fun _ _ => @eq Any.t) 100
                       (mrs_src1, URA.add fr_src1 rret, k_src vret_src) (mrs_tgt1, frs_tgt, k_tgt vret_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ (fun _ _ => @eq Any.t) n
             (([(mn, (mr_src0, mp_src0))], fr_src0),
              (HoareCall mn tbr ord_cur P Q fn varg_src) >>= k_src)
             ((mrs_tgt, frs_tgt),
              trigger (Call fn varg_tgt) >>= k_tgt).
  Proof.
    unfold HoareCall, put, discard, forge, checkWf, assume, guarantee.
    ired. gstep. econs; eauto. exists (mr_src1, URA.add rarg_src fr_src1).
    ired. gstep. econs; eauto.
    { instantiate (1:=mp_src0). instantiate (1:=mr_src0). admit "ez". }
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. split; auto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    { instantiate (1:=mp_src0). instantiate (1:=mr_src0). admit "ez". }
    ired. gstep. econs; eauto. exists rarg_src.
    ired. gstep. econs; eauto.
    replace (alist_add Dec_RelDec mn (mr_src1, mp_src0) [(mn, (mr_src0, mp_src0))]) with [(mn, (mr_src1, mp_src0))].
    2: { admit "ez". }
    ired. gstep. econs; eauto. exists fr_src1.
    ired. gstep. econs; eauto. split; auto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. exists x.
    ired. gstep. econs; eauto. exists varg_tgt.
    ired. gstep. econs; eauto. exists o.
    ired. gstep. econs; eauto. split; auto.
    ired. gstep. econs; eauto. split; auto.
    ired. gstep. econs; eauto. i. exists 108.
    ired. gstep. econs; eauto. i.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. i.
    hexploit (POST vret mrs_src1 mrs_tgt1 x0 x1 WF0). i. des.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. i.
    ired. gstep. econs; eauto.
  Qed.

  Lemma harg_clo
        r rg mr_src0 mp_src0 fr_src0
        mn X Y (P: X -> Y -> Any.t -> ord -> Σ -> Prop) varg_tgt
        mrs_tgt frs_tgt f_tgt k_src
        (wf: (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)) -> Prop)
        (ARG:
           forall x varg_src rarg_src ord_cur
                  (VALID: URA.wf (URA.add mr_src0 (URA.add fr_src0 rarg_src)))
                  (PRE: P x varg_src varg_tgt ord_cur rarg_src),
             gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ (fun _ _ => @eq Any.t) 90
                    ([(mn, (mr_src0, mp_src0))], URA.add fr_src0 rarg_src,
                     k_src (x, varg_src, ord_cur)) (mrs_tgt, frs_tgt, f_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ (fun _ _ => @eq Any.t) 100
             (([(mn, (mr_src0, mp_src0))], fr_src0),
              (HoareFunArg mn P varg_tgt >>= k_src))
             ((mrs_tgt, frs_tgt),
              f_tgt).
  Proof.
    unfold HoareFunArg, put, discard, forge, checkWf, assume, guarantee.
    ired. gstep. econs; eauto. intros varg_src.
    ired. gstep. econs; eauto. intros x.
    ired. gstep. econs; eauto. intros rarg_src.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    { instantiate (1:=mp_src0). instantiate (1:=mr_src0). admit "ez". }
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. intros VALID.
    ired. gstep. econs; eauto. intros ord_cur.
    ired. gstep. econs; eauto.
  Qed.

  Lemma hret_clo (mr_src1 rret_src: Σ)
        r rg n mr_src0 mp_src0 fr_src0
        mn X Z (Q: X -> Z -> Any.t -> Σ -> Prop)
        x vret_src vret_tgt
        mrs_tgt frs_tgt
        (wf: (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)) -> Prop)
        (FUEL: n > 14)
        (UPDATABLE: URA.updatable (URA.add mr_src0 fr_src0) (URA.add mr_src1 rret_src))
        (POST: Q x vret_src vret_tgt rret_src)
        (WF: wf ([(mn, (mr_src1, mp_src0))], mrs_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ (fun _ _ => @eq Any.t) n
             (([(mn, (mr_src0, mp_src0))], fr_src0),
              (HoareFunRet mn Q x vret_src))
             ((mrs_tgt, frs_tgt),
              (Ret vret_tgt)).
  Proof.
    unfold HoareFunRet, put, discard, forge, checkWf, assume, guarantee.
    ired. gstep. econs; eauto. exists vret_tgt.
    ired. gstep. econs; eauto. exists (mr_src1, rret_src).
    ired. gstep. econs; eauto.
    { instantiate (1:=mp_src0). instantiate (1:=mr_src0). admit "ez". }
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. split; auto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    { instantiate (1:=mp_src0). instantiate (1:=mr_src0). admit "ez". }
    ired. gstep. econs; eauto. exists rret_src.
    ired. gstep. econs; eauto. split; auto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. exists ε.
    ired. gstep. econs; eauto. split.
    { rewrite URA.unit_id. auto. }
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    replace (alist_add Dec_RelDec mn (mr_src1, mp_src0) [(mn, (mr_src0, mp_src0))]) with [(mn, (mr_src1, mp_src0))].
    2: { admit "ez". }
    auto.
  Qed.
End HLEMMAS.

Ltac _harg_tac := prep; eapply harg_clo; i.

Ltac _hcall_tac x o mr_src1 fr_src1 rarg_src := prep; eapply (@hcall_clo _ _ x o mr_src1 fr_src1 rarg_src); [|lia|..].

Ltac _hret_tac mr_src1 rret_src := prep; eapply (@hret_clo _ mr_src1 rret_src); [lia|..].

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
    | ltac_wild => eapply (hcall_clo _ (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src)); [tac0|lia|..|tac1]
    | _ => eapply (hcall_clo _ (o:=o) (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src)); [tac0|lia|..|tac1]
    end
  | _ => eapply (hcall_clo x (o:=o) (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src)); [tac0|lia|..|tac1]
  end
.

Ltac hret_tac MR_SRC RT_SRC :=
  let mr_src1 := r_gather MR_SRC in
  let fr_src1 := r_gather RT_SRC in
  let tac0 := etrans; [etrans; [|on_gwf ltac:(fun GWF => apply GWF)]|]; eapply URA.extends_updatable; r_equalize; r_solve; fail in
  _hret_tac mr_src1 fr_src1; [tac0| |]
.
