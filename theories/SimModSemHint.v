Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import ModSem.
Require Import Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Any.

From Ordinal Require Import Ordinal Arithmetic.

Set Implicit Arguments.

Local Open Scope nat_scope.












Require Import SimModSemL.

Section SIM.

  Context `{ns: gnames}.

  Let st_local: Type := (Any.t).

  Variable world: Type.

  Let W: Type := (Any.t) * (Any.t).
  Variable wf: world -> W -> Prop.
  Variable le: relation world.


  Variant _sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), Ord.t -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : Ord.t -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_ret
      i0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | sim_itree_tau
      i0 w0 st_src0 st_tgt0
      i1 i_src i_tgt
      (K: sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, tau;; i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_call
      i0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          exists i1, sim_itree _ _ RR i1 w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      _sim_itree sim_itree RR i0 w (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_syscall
      i0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          exists i1, sim_itree _ _ RR i1 w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)
  (*** TODO: sim_syscall is nontrivial; it should accept "injected" memory... ***)
  (*** TODO: simplify the model: Syscall: list val -> val ***)

  | sim_itree_choose_both
      i0 w0 st_src0 st_tgt0
      X_src X_tgt k_src k_tgt
      (K: forall (x_tgt: X_tgt), exists (x_src: X_src) i1, sim_itree _ _ RR i1 w0 (st_src0, k_src x_src) (st_tgt0, k_tgt x_tgt))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, trigger (Choose X_src) >>= k_src)
                 (st_tgt0, trigger (Choose X_tgt) >>= k_tgt)
  | sim_itree_take_both
      i0 w0 st_src0 st_tgt0
      X_src X_tgt k_src k_tgt
      (K: forall (x_src: X_src), exists (x_tgt: X_tgt) i1, sim_itree _ _ RR i1 w0 (st_src0, k_src x_src) (st_tgt0, k_tgt x_tgt))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, trigger (Take X_src) >>= k_src)
                 (st_tgt0, trigger (Take X_tgt) >>= k_tgt)
  | sim_itree_pput_both
      i0 w0
      i1 k_src k_tgt
      st_src0 st_tgt0 st_src1 st_tgt1
      (K: sim_itree _ _ RR i1 w0 (st_src1, k_src tt) (st_tgt1, k_tgt tt))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                 (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)
  | sim_itree_pget_both
      i0 w0
      i1 k_src k_tgt
      st_src0 st_tgt0
      (K: sim_itree _ _ RR i1 w0 (st_src0, k_src st_src0) (st_tgt0, k_tgt st_tgt0))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, trigger (PGet) >>= k_src)
                 (st_tgt0, trigger (PGet) >>= k_tgt)



  | sim_itree_tau_src
      i0 w0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_choose_src
      i0 w0 st_src0 st_tgt0
      i1 X k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: exists (x: X), sim_itree _ _ RR i1 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, trigger (Choose X) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itree_take_src
      i0 w0 st_src0 st_tgt0
      i1 X k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: forall (x: X), sim_itree _ _ RR i1 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, trigger (Take X) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_pput_src
      i0 w0 st_tgt0 st_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      st_src1
      (K: sim_itree _ _ RR i1 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_pget_src
      i0 w0 st_tgt0 st_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, trigger (PGet) >>= k_src)
                 (st_tgt0, i_tgt)






  | sim_itree_tau_tgt
      i0 w0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_choose_tgt
      i0 w0 st_src0 st_tgt0
      i1 X i_src k_tgt
      (ORD: Ord.lt i1 i0)
      (K: forall (x: X), sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itree_take_tgt
      i0 w0 st_src0 st_tgt0
      i1 X i_src k_tgt
      (ORD: Ord.lt i1 i0)
      (K: exists (x: X), sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Take X) >>= k_tgt)

  | sim_itree_pput_tgt
      i0 w0 st_src0 st_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      st_tgt1
      (K: sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | sim_itree_pget_tgt
      i0 w0 st_src0 st_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PGet) >>= k_tgt)
  | sim_itree_call_fail
      i0 w0 st_src0 st_tgt0
      fn varg k_src i_tgt
      (FAIL: ~ ns fn)
    :
      _sim_itree sim_itree RR i0 w0 (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, i_tgt)
  .

  Definition lift_rel {R_src R_tgt} (w0: world) (RR: R_src -> R_tgt -> Prop)
             (st_src st_tgt: st_local) (ret_src ret_tgt : Any.t) :=
    exists w1 : world,
      (<<WLE: le w0 w1 >> /\ <<WF: wf w1 (st_src, st_tgt) >> /\ <<RET: ret_src = ret_tgt >>).

  Definition sim_itree o w0: relation _ :=
    paco7 _sim_itree bot7 _ _ (lift_rel w0 (@eq Any.t)) o w0.

  Lemma sim_itree_mon: monotone7 _sim_itree.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree_mon: paco.

  Lemma sim_itree_mon_ord r S_src S_tgt SS i0 i1 (ORD: (i0 <= i1)%ord): @_sim_itree r S_src S_tgt SS i0 <3= @_sim_itree r S_src S_tgt SS i1.
  Proof.
    ii. inv PR; try (by econs; et).
    (* - econs; try apply SIM; et. etrans; et. *)
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
  Qed.

  Definition sim_fsem: relation (option mname * Any.t -> itree Es Any.t) :=
    (eq ==> (fun it_src it_tgt => forall w mrs_src mrs_tgt (SIMMRS: wf w (mrs_src, mrs_tgt)),
                 exists n, sim_itree n w (mrs_src, it_src)
                                     (mrs_tgt, it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (option mname * Any.t -> itree Es Any.t)) := RelProd eq sim_fsem.


  Variant lordC (r: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), Ord.t -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : Ord.t -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | lordC_intro
      o0 o1 w st_src st_tgt
      (ORD: Ord.le o0 o1)
      (SIM: r _ _ RR o0 w st_src st_tgt)
    :
      lordC r RR o1 w st_src st_tgt
  .
  Hint Constructors lordC: core.

  Lemma lordC_mon
        r1 r2
        (LE: r1 <7= r2)
    :
      @lordC r1 <7= @lordC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lordC_mon: paco.

  Lemma lordC_compatible: compatible7 (_sim_itree) lordC.
  Proof.
    econs; eauto with paco.
    ii. inv PR. eapply sim_itree_mon_ord; eauto.
    eapply sim_itree_mon; eauto.
    i. econs; eauto. refl.
  Qed.

  Lemma lordC_spec: lordC <8= gupaco7 (_sim_itree) (cpn7 _sim_itree).
  Proof.
    intros. gclo. econs.
    { eapply lordC_compatible. }
    ss. eapply lordC_mon; [|eauto]. i. gbase. auto.
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), Ord.t -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop):
    forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), Ord.t -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop :=
  | lbindR_intro
      o0 o1 w0 w1

      R_src R_tgt RR
      (st_src0 st_tgt0: st_local)
      (i_src: itree Es R_src) (i_tgt: itree Es R_tgt)
      (SIM: r _ _ RR o0 w0 (st_src0, i_src) (st_tgt0, i_tgt))

      S_src S_tgt SS
      (k_src: ktree Es R_src S_src) (k_tgt: ktree Es R_tgt S_tgt)
      (SIMK: forall st_src1 st_tgt1 vret_src vret_tgt (SIM: RR st_src1 st_tgt1 vret_src vret_tgt), s _ _ SS o1 w1 (st_src1, k_src vret_src) (st_tgt1, k_tgt vret_tgt))
    :
      lbindR r s SS (OrdArith.add o1 o0) w1 (st_src0, ITree.bind i_src k_src) (st_tgt0, ITree.bind i_tgt k_tgt)
  .

  Hint Constructors lbindR: core.

  Lemma lbindR_mon
        r1 r2 s1 s2
        (LEr: r1 <7= r2) (LEs: s1 <7= s2)
    :
      lbindR r1 s1 <7= lbindR r2 s2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Definition lbindC r := lbindR r r.
  Hint Unfold lbindC: core.

  Lemma lbindC_wrespectful: wrespectful7 (_sim_itree) lbindC.
  Proof.
    econstructor; repeat intro.
    { eapply lbindR_mon; eauto. }
    rename l into llll.
    eapply lbindR_mon in PR; cycle 1.
    { eapply GF. }
    { i. eapply PR0. }
    inv PR. csc. inv SIM.
    + rewrite ! bind_ret_l. exploit SIMK; eauto. i.
      eapply sim_itree_mon_ord.
      { instantiate (1:=o1). eapply OrdArith.add_base_l. }
      eapply sim_itree_mon; eauto with paco.
    + rewrite ! bind_tau. econs; eauto.
      econs 2; eauto with paco. econs; eauto with paco.
    + rewrite ! bind_bind.
      econs; eauto.
      i. exploit K; eauto. i. des. eexists.
      eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      i. exploit K; eauto. i. des. eexists.
      eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      i. exploit K; eauto. i. des. esplits.
      eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      i. exploit K; eauto. i. des. esplits.
      eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      econs 2; eauto with paco. econs; eauto with paco.
    + rewrite ! bind_bind. des. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eexists. eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      i. hexploit K; eauto. i.
      eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      econs 2; eauto with paco. econs; eauto with paco.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      i. hexploit K; eauto. i.
      eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_bind. des. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eexists. eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo7_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
  Qed.

  Lemma lbindC_spec: lbindC <8= gupaco7 (_sim_itree) (cpn7 (_sim_itree)).
  Proof.
    intros. eapply wrespect7_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

End SIM.
Hint Resolve sim_itree_mon: paco.


Lemma self_sim_itree `{ns: gnames}:
  forall n st itr,
    sim_itree (fun _ '(src, tgt) => src = tgt) top2 n tt (st, itr) (st, itr).
Proof.
  pcofix CIH. i. pfold. ides itr.
  { eapply sim_itree_ret; ss. }
  { eapply sim_itree_tau. right. eapply CIH; ss. }
  destruct e.
  { dependent destruction c. rewrite <- ! bind_trigger. eapply sim_itree_call; ss.
    ii; subst. exists 0. right. eapply CIH.
  }
  destruct s.
  { rewrite <- ! bind_trigger. dependent destruction p; econs; eauto. }
  { rewrite <- ! bind_trigger. dependent destruction e; econs; eauto. }
Unshelve.
  all: try (exact 0).
Qed.



(*** desiderata: (1) state-aware simulation relation !!!! ***)
(*** (2) not whole function frame, just my function frame !!!! ***)
(*** (3) would be great if induction tactic works !!!! (study itree case study more) ***)



Module ModSemPair.
Section SIMMODSEM.

  Context `{ns: gnames}.
  Variable (ms_src ms_tgt: ModSem.t).

  Let W: Type := (Any.t) * (Any.t).
  Inductive sim: Prop := mk {
    world: Type;
    wf: world -> W -> Prop;
    le: world -> world -> Prop;
    le_PreOrder: PreOrder le;
    sim_fnsems: Forall2 (sim_fnsem wf le) ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems);
    sim_mn: ms_src.(ModSem.mn) = ms_tgt.(ModSem.mn);
    sim_initial: exists w_init, wf w_init (ms_src.(ModSem.initial_st), ms_tgt.(ModSem.initial_st));
  }.

End SIMMODSEM.

Lemma self_sim `{ns: gnames} (ms: ModSem.t):
  sim ms ms.
Proof.
  econs; et.
  - instantiate (1:=fun (_ _: unit) => True). ss.
  - instantiate (1:=(fun (_: unit) '(src, tgt) => src = tgt)). (* fun p => fst p = snd p *)
    generalize (ModSem.fnsems ms).
    induction l; ii; ss.
    econs; eauto. econs; ss. ii; clarify.
    destruct w. exploit self_sim_itree; et.
  - ss.
Unshelve.
all: try (exact 0).
Qed.

End ModSemPair.





Section ADQ.

  Context `{ns: gnames}.

  Variable ms_src ms_tgt: ModSem.t.

  Let wf_lift world (wf: (world -> (Any.t) * (Any.t) -> Prop)): world -> (alist string (Any.t) * alist string (Any.t) -> Prop) :=
    (fun w '(mrs_src, mrs_tgt) =>
       exists mp_src mp_tgt,
         (<<SRC: mrs_src = Maps.add ms_src.(ModSem.mn) mp_src Maps.empty>>) /\
         (<<TGT: mrs_tgt = Maps.add ms_tgt.(ModSem.mn) mp_tgt Maps.empty>>) /\
         (<<WF: wf w (mp_src, mp_tgt)>>)
    )
  .

  Lemma adequacy_lift_itree
        world (wf: world -> ((Any.t) * (Any.t) -> Prop))
        (le: world -> world -> Prop)
        n w st_src0 i_src0 st_tgt0 i_tgt0
        (MN: ms_src.(ModSem.mn) = ms_tgt.(ModSem.mn))
        (SIM: sim_itree wf le n w (st_src0, i_src0) (st_tgt0, i_tgt0))
    :
      <<SIM: SimModSemL.sim_itree (wf_lift wf) le (2 * n)%ord w ([(ModSem.mn ms_src, (st_src0))], transl_all (ModSem.mn ms_src) i_src0)
                       ([(ModSem.mn ms_tgt, (st_tgt0))], transl_all (ModSem.mn ms_tgt) i_tgt0)>>
  .
  Proof.
    r. ginit.
    { eapply cpn7_wcompat. eauto with paco. }
    revert_until wf. gcofix CIH. i.
    punfold SIM. dependent destruction SIM.
    - unfold transl_all. rewrite ! unfold_interp. ss. gstep. econs; eauto.
      red in RET. ss. des. subst. esplits; et.
    - unfold transl_all. rewrite ! unfold_interp. ss. gstep. econs; eauto.
      pclearbot. gbase. eapply CIH; et.
    - unfold transl_all. rewrite ! interp_bind. rewrite ! unfold_interp. ss. rewrite ! bind_bind.
      replace (r1 <- trigger (EventsL.Call (Some (ModSem.mn ms_src)) fn varg);; x <- (Ret r1);;
               x0 <- (tau;; interp (handle_all (ModSem.mn ms_src)) (Ret x));; interp (handle_all (ModSem.mn ms_src)) (k_src x0)) with
          (r <- trigger (EventsL.Call (Some (ModSem.mn ms_src)) fn varg);; tau;; (interp (handle_all (ModSem.mn ms_src)) (k_src r))); cycle 1.
      { grind. }
      replace (r1 <- trigger (EventsL.Call (Some (ModSem.mn ms_tgt)) fn varg);; x <- (Ret r1);;
               x0 <- (tau;; interp (handle_all (ModSem.mn ms_tgt)) (Ret x));; interp (handle_all (ModSem.mn ms_tgt)) (k_tgt x0)) with
          (r <- trigger (EventsL.Call (Some (ModSem.mn ms_src)) fn varg);; tau;; (interp (handle_all (ModSem.mn ms_tgt)) (k_tgt r))); cycle 1.
      { rewrite MN. grind. }
      gstep. econs; eauto.
      { rr. esplits; ss; et. }
      ii. ss. des; ss. subst. unfold alist_add. ss.
      exploit K; et. i; des. pclearbot. exists (2 * i1)%ord.
      replace (interp (handle_all (ModSem.mn ms_src))) with (transl_all (ModSem.mn ms_src)) by refl.
      replace (interp (handle_all (ModSem.mn ms_tgt))) with (transl_all (ModSem.mn ms_tgt)) by refl.
      gbase. eapply CIH; et.
    - unfold transl_all. rewrite ! unfold_interp. ired.
      gstep. econs; et. ii. exploit K; et. i; des. pclearbot. esplits; et. ired. gstep. econs; et. gbase. eapply CIH; et.
    - unfold transl_all. rewrite ! unfold_interp. ired.
      gstep. econs; et. ii. exploit K; et. i; des. pclearbot. esplits; et. ired. gstep. econs; et. gbase. eapply CIH; et.
    - unfold transl_all. rewrite ! unfold_interp. ired.
      gstep. econs; et. ii. exploit K; et. i; des. pclearbot. esplits; et. ired. gstep. econs; et. gbase. eapply CIH; et.
    - unfold transl_all. rewrite ! unfold_interp. ired.
      rewrite <- MN. gstep. econs; ss; et.
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      unfold alist_add; ss. des_ifs.
      { bsimpl. unfold rel_dec in *. ss. des_sumbool; ss. }
      ired. gstep; econs; et. pclearbot. gbase.
      match goal with | [ |- r _ _ _ _ _ ?x _ ] => remember x as tmp end.
      subst tmp. rewrite MN in *. eapply CIH; et.
    - unfold transl_all. rewrite ! unfold_interp. ired.
      rewrite <- MN. gstep. econs; ss; et.
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      ired. gstep; econs; et. pclearbot. gbase.
      match goal with | [ |- r _ _ _ _ _ ?x _ ] => remember x as tmp end.
      subst tmp. rewrite MN in *. eapply CIH; et.


    (***** SRC *****)
    - unfold transl_all. rewrite unfold_interp. ired.
      gstep. econs; et.
      { eapply OrdArith.lt_mult_r; et. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      pclearbot.
      gbase. eapply CIH; et.
    - unfold transl_all. rewrite unfold_interp. ired.
      des. pclearbot. gstep. econs; et.
      { instantiate (1:=(2 * i1 + 1)%ord). eapply Ord.S_is_S in ORD. eapply Ord.lt_le_lt; cycle 1.
        { rewrite <- ORD. refl. }
        assert(T: ((Ord.S i1) == (i1 + 1))%ord).
        { rewrite Ord.from_nat_S. rewrite OrdArith.add_S. ss. rewrite OrdArith.add_O_r. refl. }
        rewrite T. rewrite OrdArith.mult_dist.
        rewrite OrdArith.mult_1_r.
        eapply OrdArith.lt_add_r. eapply OrdArith.lt_from_nat. lia.
      }
      esplits. ired. gstep; econs; et.
      { eapply OrdArith.add_lt_l. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      gbase. eapply CIH; et.
    - unfold transl_all. rewrite unfold_interp. ired.
      gstep. econs; et.
      { instantiate (1:=(2 * i1 + 1)%ord). eapply Ord.S_is_S in ORD. eapply Ord.lt_le_lt; cycle 1.
        { rewrite <- ORD. refl. }
        assert(T: ((Ord.S i1) == (i1 + 1))%ord).
        { rewrite Ord.from_nat_S. rewrite OrdArith.add_S. ss. rewrite OrdArith.add_O_r. refl. }
        rewrite T. rewrite OrdArith.mult_dist.
        rewrite OrdArith.mult_1_r.
        eapply OrdArith.lt_add_r. eapply OrdArith.lt_from_nat. lia.
      }
      i. spc K. pclearbot.
      esplits. ired. gstep; econs; et.
      { eapply OrdArith.add_lt_l. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      gbase. eapply CIH; et.
    - unfold transl_all. rewrite unfold_interp. ired.
      pclearbot.
      gstep. econs; ss; et.
      { instantiate (1:=(2 * i1 + 1)%ord). eapply Ord.S_is_S in ORD. eapply Ord.lt_le_lt; cycle 1.
        { rewrite <- ORD. refl. }
        assert(T: ((Ord.S i1) == (i1 + 1))%ord).
        { rewrite Ord.from_nat_S. rewrite OrdArith.add_S. ss. rewrite OrdArith.add_O_r. refl. }
        rewrite T. rewrite OrdArith.mult_dist.
        rewrite OrdArith.mult_1_r.
        eapply OrdArith.lt_add_r. eapply OrdArith.lt_from_nat. lia.
      }
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      gstep. econs; ss; et.
      { eapply OrdArith.add_lt_l. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      unfold alist_add. ss. unfold rel_dec. ss. des_ifs.
      { bsimpl. des_sumbool; ss. }
      ired. gbase. eapply CIH; et.
    - unfold transl_all. rewrite unfold_interp. ired.
      pclearbot.
      gstep. econs; ss; et.
      { instantiate (1:=(2 * i1 + 1)%ord). eapply Ord.S_is_S in ORD. eapply Ord.lt_le_lt; cycle 1.
        { rewrite <- ORD. refl. }
        assert(T: ((Ord.S i1) == (i1 + 1))%ord).
        { rewrite Ord.from_nat_S. rewrite OrdArith.add_S. ss. rewrite OrdArith.add_O_r. refl. }
        rewrite T. rewrite OrdArith.mult_dist.
        rewrite OrdArith.mult_1_r.
        eapply OrdArith.lt_add_r. eapply OrdArith.lt_from_nat. lia.
      }
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      gstep. econs; ss; et.
      { eapply OrdArith.add_lt_l. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      ired. gbase. eapply CIH; et.


    (***** TGT *****)
    - unfold transl_all. match goal with | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
      rewrite unfold_interp. ired. subst.
      gstep. econs; et.
      { eapply OrdArith.lt_mult_r; et. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      pclearbot.
      gbase. eapply CIH; et.
    - unfold transl_all. match goal with | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
      rewrite unfold_interp. ired. subst.
      gstep. econs; et.
      { instantiate (1:=(2 * i1 + 1)%ord). eapply Ord.S_is_S in ORD. eapply Ord.lt_le_lt; cycle 1.
        { rewrite <- ORD. refl. }
        assert(T: ((Ord.S i1) == (i1 + 1))%ord).
        { rewrite Ord.from_nat_S. rewrite OrdArith.add_S. ss. rewrite OrdArith.add_O_r. refl. }
        rewrite T. rewrite OrdArith.mult_dist.
        rewrite OrdArith.mult_1_r.
        eapply OrdArith.lt_add_r. eapply OrdArith.lt_from_nat. lia.
      }
      i. spc K. pclearbot.
      esplits. ired. gstep; econs; et.
      { eapply OrdArith.add_lt_l. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      gbase. eapply CIH; et.
    - unfold transl_all. match goal with | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
      rewrite unfold_interp. ired. subst.
      des. pclearbot. gstep. econs; et.
      { instantiate (1:=(2 * i1 + 1)%ord). eapply Ord.S_is_S in ORD. eapply Ord.lt_le_lt; cycle 1.
        { rewrite <- ORD. refl. }
        assert(T: ((Ord.S i1) == (i1 + 1))%ord).
        { rewrite Ord.from_nat_S. rewrite OrdArith.add_S. ss. rewrite OrdArith.add_O_r. refl. }
        rewrite T. rewrite OrdArith.mult_dist.
        rewrite OrdArith.mult_1_r.
        eapply OrdArith.lt_add_r. eapply OrdArith.lt_from_nat. lia.
      }
      esplits. ired. gstep; econs; et.
      { eapply OrdArith.add_lt_l. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      gbase. eapply CIH; et.
    - unfold transl_all. match goal with | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
      rewrite unfold_interp. ired. subst.
      pclearbot.
      gstep. econs; ss; et.
      { instantiate (1:=(2 * i1 + 1)%ord). eapply Ord.S_is_S in ORD. eapply Ord.lt_le_lt; cycle 1.
        { rewrite <- ORD. refl. }
        assert(T: ((Ord.S i1) == (i1 + 1))%ord).
        { rewrite Ord.from_nat_S. rewrite OrdArith.add_S. ss. rewrite OrdArith.add_O_r. refl. }
        rewrite T. rewrite OrdArith.mult_dist.
        rewrite OrdArith.mult_1_r.
        eapply OrdArith.lt_add_r. eapply OrdArith.lt_from_nat. lia.
      }
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      gstep. econs; ss; et.
      { eapply OrdArith.add_lt_l. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      unfold alist_add. ss. unfold rel_dec. ss. des_ifs.
      { bsimpl. des_sumbool; ss. }
      ired. gbase. eapply CIH; et.
    - unfold transl_all. match goal with | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
      rewrite unfold_interp. ired. subst.
      pclearbot.
      gstep. econs; ss; et.
      { instantiate (1:=(2 * i1 + 1)%ord). eapply Ord.S_is_S in ORD. eapply Ord.lt_le_lt; cycle 1.
        { rewrite <- ORD. refl. }
        assert(T: ((Ord.S i1) == (i1 + 1))%ord).
        { rewrite Ord.from_nat_S. rewrite OrdArith.add_S. ss. rewrite OrdArith.add_O_r. refl. }
        rewrite T. rewrite OrdArith.mult_dist.
        rewrite OrdArith.mult_1_r.
        eapply OrdArith.lt_add_r. eapply OrdArith.lt_from_nat. lia.
      }
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      gstep. econs; ss; et.
      { eapply OrdArith.add_lt_l. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      ired. gbase. eapply CIH; et.
    - unfold transl_all. rewrite ! interp_bind. rewrite ! unfold_interp. ss. rewrite ! bind_bind.
      replace (r1 <- trigger (EventsL.Call (Some (ModSem.mn ms_src)) fn varg);; x <- (Ret r1);;
               x0 <- (tau;; interp (handle_all (ModSem.mn ms_src)) (Ret x));; interp (handle_all (ModSem.mn ms_src)) (k_src x0)) with
          (r <- trigger (EventsL.Call (Some (ModSem.mn ms_src)) fn varg);; tau;; (interp (handle_all (ModSem.mn ms_src)) (k_src r))); cycle 1.
      { grind. }
      gstep. econs. auto.
      Unshelve.
      all: exact 0.
  Qed.

  Lemma adequacy_lift_fsem
        world wf (le: world -> world -> Prop) f_src f_tgt
        (MN: ms_src.(ModSem.mn) = ms_tgt.(ModSem.mn))
        (SIM: sim_fsem wf le f_src f_tgt)
    :
      SimModSemL.sim_fsem (wf_lift wf) le (fun args => transl_all ms_src.(ModSem.mn) (f_src args))
                          (fun args => transl_all ms_tgt.(ModSem.mn) (f_tgt args))
  .
  Proof.
    ii. clarify. rr in SIM. specialize (SIM y y eq_refl).
    r in SIMMRS. des. ss. subst. unfold alist_add in *. ss. clarify.
    specialize (SIM w mp_src mp_tgt).
    exploit SIM; et. i; des.
    esplits. eapply adequacy_lift_itree; ss; et.
  Qed.

  Theorem adequacy_lift
          (SIM: ModSemPair.sim ms_src ms_tgt)
    :
      <<SIM: ModSemLPair.sim ms_src ms_tgt>>
  .
  Proof.
    inv SIM.
    right. econs.
    { eapply le_PreOrder. }
    { instantiate (1:=wf_lift wf).
      ss.
      eapply Forall2_apply_Forall2; et.
      i. destruct a, b; ss. rr in H. des; ss. rr in H. r in H0. ss. clarify.
      split; ss. r. ss.
      eapply adequacy_lift_fsem; et.
    }
    { des. ss. esplits; ss; et. }
    { ss. rewrite sim_mn. auto. }
  Qed.

End ADQ.




Module ModPair.
Section SIMMOD.
   Context `{ns: sk_gnames}.
   Variable (md_src md_tgt: Mod.t).
   Inductive sim: Prop := mk {
     sim_modsem:
       forall sk
              (SKINCL: Sk.incl md_tgt.(Mod.sk) sk)
              (SKWF: Sk.wf sk),
         <<SIM: ModSemPair.sim (ns:=sk_gnames_contents sk) (md_src.(Mod.get_modsem) sk) (md_tgt.(Mod.get_modsem) sk)>>;
     sim_sk: <<SIM: md_src.(Mod.sk) = md_tgt.(Mod.sk)>>;
   }.

End SIMMOD.

Lemma self_sim `{ns: sk_gnames} (md: Mod.t):
  sim md md.
Proof.
  econs; et. i.
  eapply ModSemPair.self_sim.
Qed.

End ModPair.



Section SIMMOD.

  Lemma Forall2_eq_eq A (l0 l1: list A)
        (FORALL: Forall2 eq l0 l1)
    :
      l0 = l1.
  Proof.
    revert l1 FORALL. induction l0; ss.
    { i. inv FORALL. ss. }
    { i. inv FORALL. f_equal; auto. }
  Qed.

  Lemma nodup_app A (l0 l1: list A)
        (ND: NoDup (l0 ++ l1))
    :
      NoDup l0 /\ NoDup l1.
  Proof.
    revert l0 ND. induction l0; ss.
    { i. split; auto. econs. }
    { i. inv ND. hexploit IHl0; et. i. des. split; auto.
      econs; et. ii. eapply H1.
      eapply in_or_app; et. }
  Qed.

  Lemma modsem_fnsems_lift_fst (md: ModSem.t)
    :
      List.map fst (ModSemL.fnsems (ModSem.lift md))
      =
      List.map fst (ModSem.fnsems md).
  Proof.
    ss. rewrite List.map_map. induction (ModSem.fnsems md); ss.
    destruct a. rewrite IHl. ss.
  Qed.

  Lemma lift_wf_function (ms: ModSem.t) itr
    :
      wf_function
        (List.map fst (ModSemL.initial_mrs (ModSem.lift ms)))
        (transl_all (ModSem.mn ms) itr).
  Proof.
    revert itr. pcofix CIH. i. unfold transl_all. ides itr.
    { rewrite interp_ret. pfold. econs 1; et. }
    { rewrite interp_tau. pfold. econs 2; et. }
    rewrite <- bind_trigger. rewrite interp_bind.
    rewrite interp_trigger. rewrite ! bind_bind.
    destruct e.
    { ss. destruct c. ss. rewrite ! bind_bind.
      pfold. eapply wf_function_call.
      { instantiate (1:=args).
        instantiate (1:=fn).
        instantiate (1:=ms.(ModSem.mn)).
        instantiate (1:=fun r0 => interp (handle_all (ModSem.mn ms)) (k r0)).
        grind. }
      { ss. auto. }
      i. right. grind. eapply CIH.
    }
    destruct s.
    { ss. destruct p; ss.
      { pfold. eapply wf_function_pput.
        { f_equal. extensionality u. rewrite bind_tau. ss. }
        { ss. auto. }
        i. left. pfold. eapply wf_function_tau; ss.
        right. rewrite bind_ret_l. eapply CIH.
      }
      { pfold. eapply wf_function_pget.
        { f_equal. extensionality u. rewrite bind_tau. ss. }
        { ss. auto. }
        i. left. pfold. eapply wf_function_tau; ss.
        right. rewrite bind_ret_l. eapply CIH.
      }
    }
    destruct e.
    { pfold. eapply wf_function_choose.
      { f_equal. extensionality u. rewrite bind_tau. ss. }
      i. left. pfold. eapply wf_function_tau; ss.
      right. rewrite bind_ret_l. eapply CIH.
    }
    { pfold. eapply wf_function_take.
      { f_equal. extensionality u. rewrite bind_tau. ss. }
      i. left. pfold. eapply wf_function_tau; ss.
      right. rewrite bind_ret_l. eapply CIH.
    }
    { pfold. ss. eapply wf_function_syscall.
      { f_equal. extensionality u. rewrite bind_tau. ss. }
      i. left. pfold. eapply wf_function_tau; ss.
      right. rewrite bind_ret_l. eapply CIH.
    }
  Qed.

  Lemma lift_list_wf_function sk ctx
    :
      Forall
        (fun '(_, fn) =>
           forall arg,
             wf_function
               (List.map fst (ModSemL.initial_mrs (ModL.get_modsem (Mod.add_list ctx) sk)))
               (fn arg)) (ModSemL.fnsems (ModL.get_modsem (Mod.add_list ctx) sk)).
  Proof.
    induction ctx; ss. eapply Forall_app; cycle 1.
    { eapply Forall_impl; [|et].
      i. destruct a0. i. eapply wf_function_mon; [|et].
      i. ss. auto. }
    eapply Forall_forall. i.
    unfold ModSem.map_snd in *.
    eapply in_map_iff in H. des. destruct x0. subst. i.
    eapply wf_function_mon.
    2: { eapply lift_wf_function. }
    i. ss. des; ss; auto.
  Qed.

  Context {CONF: EMSConfig}.

  Theorem adequacy_hint_aux `{ns: sk_gnames} (md_src md_tgt: Mod.t) ctx
          (NAMESPACE:
             forall sk fn
                    (SOME: is_some (alist_find fn (ModSemL.fnsems (ModL.get_modsem (ModL.add (Mod.add_list ctx) md_src) sk)))),
               sk_gnames_contents sk fn)
           (SIM: ModPair.sim md_src md_tgt)
     :
       Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) md_tgt))
       <1=
       Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) md_src)).
   Proof.
     ii. destruct (classic (ModL.wf (ModL.add (Mod.add_list ctx) md_src))).
     2: { unfold ModL.compile. eapply ModSemL.initial_itr_not_wf. auto. }
     rename H into WFSRC.
     assert (SKEQ: Sk.add (ModL.sk (Mod.add_list ctx)) (Mod.sk md_src)
                   =
                   Sk.add (ModL.sk (Mod.add_list ctx)) (Mod.sk md_tgt)).
     {  f_equal. inv SIM. ss. }

     hexploit SIM.(ModPair.sim_modsem).
     { instantiate (1:=Sk.sort (Sk.add (ModL.sk (Mod.add_list ctx)) (Mod.sk md_tgt))).
       etrans.
       2: { eapply Sk.sort_incl. }
       ii. eapply in_or_app. et.
     }
     { eapply Sk.sort_wf. rewrite <- SKEQ. eapply WFSRC. }
     intros SIMSEM.

     assert (WFTGT: ModL.wf (ModL.add (Mod.add_list ctx) md_tgt)).
     { red in WFSRC. red. unfold ModL.enclose in *. ss. des.
       rewrite SKEQ in *. split; auto. inv WF.
       Local Opaque ModSem.lift. econs.
       { clear wf_initial_mrs.
         ss. rewrite List.map_app in *.
         match goal with
         | H: NoDup (_ ++ ?l0) |- NoDup (_ ++ ?l1) => replace l1 with l0
         end; auto.
         inv SIMSEM.
         eapply (Forall2_apply_Forall2 fst fst) in sim_fnsems.
         { instantiate (1:=eq) in sim_fnsems.
           eapply Forall2_eq_eq; et.
           clear - sim_fnsems. rewrite ! modsem_fnsems_lift_fst. auto.
         }
         { i. inv H. ss. }
       }
       { ss. clear wf_fnsems. rewrite List.map_app in *.
         match goal with
         | H: NoDup (_ ++ ?l0) |- NoDup (_ ++ ?l1) => replace l1 with l0
         end; auto.
         Local Transparent ModSem.lift. ss.
         remember (Sk.sort (Sk.add (ModL.sk (Mod.add_list ctx)) (Mod.sk md_tgt))).
         inv SIMSEM. clear - sim_mn.
         rewrite sim_mn. auto.
       }
     }

     eapply ModLPair.adequacy_local_closed; eauto. econs.
     { ss. red.
       eapply ModSemLPair.add_modsempair.
       { rewrite SKEQ. eapply ModSemLPair.self_sim_mod. split.
         { inv WFTGT. clear - H. unfold ModL.enclose in *.
           remember (Mod.add_list ctx). clear Heqt. ss. inv H. ss.
           rewrite List.map_app in *.
           eapply nodup_app in wf_initial_mrs. des. auto.
         }
         { remember (Sk.sort (Sk.add (ModL.sk (Mod.add_list ctx)) (Mod.sk md_tgt))) as sk. clear.
           eapply lift_list_wf_function.
         }
       }
       { eapply adequacy_lift; et.
         rewrite SKEQ. auto. }
     }
     { ss. }
     { i. hexploit (@SIM.(ModPair.sim_modsem)).
       { instantiate (1:=sk). etrans; et. ss.
         inv SIM. rewrite sim_sk. clear.
         ii. eapply in_or_app. auto. }
       { auto. }
       i. inv H. inv WF. econs.
       { Local Opaque ModSem.lift.
         ss. rewrite List.map_app in *. clear wf_initial_mrs.
         match goal with
         | H: NoDup (_ ++ ?l0) |- NoDup (_ ++ ?l1) => replace l1 with l0
         end; auto.
         rewrite ! modsem_fnsems_lift_fst.
         eapply (Forall2_apply_Forall2 fst fst) in sim_fnsems.
         { instantiate (1:=eq) in sim_fnsems.
           eapply Forall2_eq_eq; et.
         }
         { i. destruct a, b. inv H. ss. }
       }
       { ss. clear wf_fnsems. rewrite List.map_app in *.
         match goal with
         | H: NoDup (_ ++ ?l0) |- NoDup (_ ++ ?l1) => replace l1 with l0
         end; auto.
         Local Transparent ModSem.lift. ss. rewrite sim_mn. auto.
       }
     }
   Qed.

   Lemma ModL_add_fnsems md0 md1 sk
     :
       (ModSemL.fnsems (ModL.get_modsem (ModL.add md0 md1) sk)) =
       (ModSemL.fnsems (ModL.get_modsem md0 sk)) ++ (ModSemL.fnsems (ModL.get_modsem md1 sk)).
   Proof.
     ss.
   Qed.

   Lemma ModL_add_sk md0 md1
     :
       ModL.sk (ModL.add md0 md1) = ModL.sk md0 ++ ModL.sk md1.
   Proof.
     ss.
   Qed.

   Lemma Mod_list_incl_sk (mds: list Mod.t) md
         (IN: In md mds)
     :
       Sk.incl (Mod.sk md) (ModL.sk (Mod.add_list mds)).
   Proof.
     rewrite Mod.add_list_sk. revert IN. induction mds; ss.
     i. des; clarify.
     { ii. eapply in_or_app. auto. }
     { ii. eapply in_or_app. right. eapply IHmds; et. }
   Qed.

   Lemma Mod_add_list_get_modsem (mds: list Mod.t) sk
     :
       ModL.get_modsem (Mod.add_list mds) sk
       =
       fold_right ModSemL.add {| ModSemL.fnsems := []; ModSemL.initial_mrs := [] |}
                  (List.map (fun (md: Mod.t) => ModL.get_modsem md sk) mds).
   Proof.
     induction mds; ss. f_equal. rewrite <- IHmds. ss.
   Qed.

   Lemma fold_right_app_flat_map A B (f: A -> list B) l
     :
       flat_map f l
       =
       fold_right (@app _) [] (List.map f l).
   Proof.
     induction l; ss. f_equal. auto.
   Qed.

   Lemma map_flat_map A B C (f: A -> list B) (g: B -> C) (l: list A)
     :
       List.map g (flat_map f l)
       =
       flat_map (List.map g) (List.map f l).
   Proof.
     induction l; ss. rewrite List.map_app. f_equal; auto.
   Qed.

   Lemma flat_map_single A B (f: A -> B) (l: list A)
     :
       flat_map (fun a => [f a]) l
       =
       List.map f l.
   Proof.
     induction l; ss.
   Qed.

   Theorem adequacy_hint `{ns: sk_gnames} mds_src mds_tgt
          (NAMESPACE:
             forall sk fn
                    (SOME: is_some (alist_find fn (ModSemL.fnsems (ModL.get_modsem (Mod.add_list mds_src) sk)))),
               sk_gnames_contents sk fn)
           (SIM: List.Forall2 ModPair.sim mds_src mds_tgt)
     :
       Beh.of_program (ModL.compile (Mod.add_list mds_tgt))
       <1=
       Beh.of_program (ModL.compile (Mod.add_list mds_src)).
   Proof.
     ii. destruct (classic (ModSemL.wf (ModL.enclose (Mod.add_list mds_src)) /\ Sk.wf (ModL.sk (Mod.add_list mds_src)))).
     2: { unfold ModL.compile. eapply ModSemL.initial_itr_not_wf. auto. }
     rename H into WF.

     assert (SKEQ: ModL.sk (Mod.add_list mds_tgt) = ModL.sk (Mod.add_list mds_src)).
     { rewrite ! Mod.add_list_sk. f_equal. symmetry.
       eapply Forall2_eq_eq. eapply Forall2_apply_Forall2; et.
       i. inv H. ss. }

     eapply ModLPair.adequacy_local_closed; et.
     unfold ModL.enclose in WF.

     econs.
     2:{
       rewrite ! Mod.add_list_sk. red. f_equal.
       clear - SIM. induction SIM; ss. inv H. f_equal; auto. }
     2: {
       i. inv WF0. econs.
       { clear wf_initial_mrs.
         match goal with
         | H: NoDup ?l0 |- NoDup ?l1 => replace l1 with l0
         end; auto.

         rewrite ! Mod.add_list_fns. f_equal.
         eapply Forall2_eq_eq.
         eapply Forall2_apply_Forall2; et.
         i. inv H. hexploit sim_modsem; et.
         { etrans; et. rewrite <- SKEQ. eapply Mod_list_incl_sk; et. }
         i. inv H. ss. rewrite ! List.map_map.
         eapply Forall2_eq_eq. eapply Forall2_apply_Forall2; et.
         i. inv H. destruct a0, b0. ss.
       }
       { clear wf_fnsems.
         match goal with
         | H: NoDup ?l0 |- NoDup ?l1 => replace l1 with l0
         end; auto.
         rewrite ! Mod.add_list_initial_mrs.
         rewrite <- ! fold_right_app_flat_map.
         ss. rewrite ! flat_map_single. rewrite ! List.map_map.
         eapply Forall2_eq_eq.
         eapply Forall2_apply_Forall2; et.
         i. ss. inv H. hexploit sim_modsem; et.
         { etrans; et. rewrite <- SKEQ. eapply Mod_list_incl_sk; et. }
         i. inv H. ss.
       }
     }
     { des. clear - SIM WF0 SKEQ. unfold ModL.enclose.
       remember (Sk.sort (ModL.sk (Mod.add_list mds_src))) as sk.
       rewrite ! Mod_add_list_get_modsem.
       eapply Forall2_apply_Forall2 with
           (f := (fun md => (Mod.lift md).(ModL.get_modsem) sk))
           (g := (fun md => (Mod.lift md).(ModL.get_modsem) sk))
           (Q:= ModSemLPair.sim)
         in SIM.
       2: {
         i. inv H. ss. eapply adequacy_lift. eapply sim_modsem.
         { etrans; [|eapply Sk.sort_incl]. rewrite <- SKEQ. eapply Mod_list_incl_sk; et. }
         { eapply Sk.sort_wf. auto. }
       }

       rewrite SKEQ in *. rewrite <- Heqsk in *. clear Heqsk.
       induction SIM; ss.
       { right. econs.
         { instantiate (1:=top2). ss. }
         { ss. }
         { exists tt. instantiate (1:=top2). ss. }
         { ss. }
       }
       { eapply ModSemLPair.add_modsempair; ss. }
     }
   Qed.

End SIMMOD.

Section SIMMOD.
   Local Existing Instances top_sk_gnames.

   Theorem adequacy_local_strong md_src md_tgt
           (SIM: ModPair.sim md_src md_tgt)
     :
       <<CR: (refines_strong md_tgt md_src)>>
   .
   Proof.
     ii. replace (ModL.add (Mod.add_list ctx) md_src) with
         (Mod.add_list (ctx ++ [md_src])).
     2: { rewrite Mod.add_list_app. rewrite Mod.add_list_single. auto. }
     replace (ModL.add (Mod.add_list ctx) md_tgt) with
         (Mod.add_list (ctx ++ [md_tgt])) in PR.
     2: { rewrite Mod.add_list_app. rewrite Mod.add_list_single. auto. }
     eapply adequacy_hint; et; ss.
     eapply Forall2_app.
     { clear. induction ctx; ss. econs; et. eapply ModPair.self_sim. }
     { econs; ss. }
   Qed.

   Context {CONF: EMSConfig}.

   Theorem adequacy_local md_src md_tgt
           (SIM: ModPair.sim md_src md_tgt)
     :
       <<CR: (refines md_tgt md_src)>>
   .
   Proof.
     eapply ModSem.refines_strong_refines.
     eapply adequacy_local_strong; et.
   Qed.

   Corollary adequacy_local_list_strong
             mds_src mds_tgt
             (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt)
     :
       <<CR: refines_strong (Mod.add_list mds_tgt) (Mod.add_list mds_src)>>
   .
   Proof.
     r. induction FORALL; ss.
     { ii. auto. }
     rewrite ! Mod.add_list_cons.
     etrans.
     { rewrite <- Mod.add_list_single. eapply refines_strong_proper_r.
       rewrite ! Mod.add_list_single. eapply adequacy_local_strong; et. }
     replace (Mod.lift x) with (Mod.add_list [x]); cycle 1.
     { cbn. rewrite ModL.add_empty_r. refl. }
     eapply refines_strong_proper_l; et.
   Qed.

   Corollary adequacy_local_list
             mds_src mds_tgt
             (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt)
     :
       <<CR: refines (Mod.add_list mds_tgt) (Mod.add_list mds_src)>>
   .
   Proof.
     eapply ModSem.refines_strong_refines.
     eapply adequacy_local_list_strong; et.
   Qed.

End SIMMOD.
