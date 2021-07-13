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










Existing Instance top_gnames.

Section SIM.
  Let st_local: Type := (Any.t).

  Variable world: Type.

  Let W: Type := (Any.t) * (Any.t).
  Variable wf: world -> W -> Prop.
  Variable le: relation world.


  Variant _sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), Ord.t -> Ord.t -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : Ord.t -> Ord.t -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | sim_itree_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          exists i_src1 i_tgt1, sim_itree _ _ RR i_src1 i_tgt1 w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          exists i_src1 i_tgt1, sim_itree _ _ RR i_src1 i_tgt1 w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itree_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src1 i_tgt1 i_src i_tgt
      (ORD: Ord.lt i_tgt1 i_tgt0)
      (K: sim_itree _ _ RR i_src1 i_tgt1 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src1 i_tgt1 X k_src i_tgt
      (ORD: Ord.lt i_tgt1 i_tgt0)
      (K: exists (x: X), sim_itree _ _ RR i_src1 i_tgt1 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itree_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src1 i_tgt1 X k_src i_tgt
      (ORD: Ord.lt i_tgt1 i_tgt0)
      (K: forall (x: X), sim_itree _ _ RR i_src1 i_tgt1 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_pput_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      i_src1 i_tgt1 k_src i_tgt
      (ORD: Ord.lt i_tgt1 i_tgt0)
      st_src1
      (K: sim_itree _ _ RR i_src1 i_tgt1 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_pget_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      i_src1 i_tgt1 k_src i_tgt
      (ORD: Ord.lt i_tgt1 i_tgt0)
      (K: sim_itree _ _ RR i_src1 i_tgt1 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
                 (st_tgt0, i_tgt)






  | sim_itree_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src1 i_tgt1 i_src i_tgt
      (ORD: Ord.lt i_src1 i_src0)
      (K: sim_itree _ _ RR i_src1 i_tgt1 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src1 i_tgt1 X i_src k_tgt
      (ORD: Ord.lt i_src1 i_src0)
      (K: forall (x: X), sim_itree _ _ RR i_src1 i_tgt1 w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itree_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src1 i_tgt1 X i_src k_tgt
      (ORD: Ord.lt i_src1 i_src0)
      (K: exists (x: X), sim_itree _ _ RR i_src1 i_tgt1 w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Take X) >>= k_tgt)

  | sim_itree_pput_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src1 i_tgt1 k_tgt i_src
      (ORD: Ord.lt i_src1 i_src0)
      st_tgt1
      (K: sim_itree _ _ RR i_src1 i_tgt1 w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | sim_itree_pget_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src1 i_tgt1 k_tgt i_src
      (ORD: Ord.lt i_src1 i_src0)
      (K: sim_itree _ _ RR i_src1 i_tgt1 w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PGet) >>= k_tgt)
  .

  Definition lift_rel {R_src R_tgt} (w0: world) (RR: R_src -> R_tgt -> Prop)
             (st_src st_tgt: st_local) (ret_src ret_tgt : Any.t) :=
    exists w1 : world,
      (<<WLE: le w0 w1 >> /\ <<WF: wf w1 (st_src, st_tgt) >> /\ <<RET: ret_src = ret_tgt >>).

  Definition sim_itree o_src o_tgt w0: relation _ :=
    paco8 _sim_itree bot8 _ _ (lift_rel w0 (@eq Any.t)) o_src o_tgt w0.

  Lemma sim_itree_mon: monotone8 _sim_itree.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree_mon: paco.

  Lemma sim_itree_mon_ord r S_src S_tgt SS i_src0 i_src1 i_tgt0 i_tgt1
        (ORDSRC: (i_src0 <= i_src1)%ord) (ORDTGT: (i_tgt0 <= i_tgt1)%ord):
    @_sim_itree r S_src S_tgt SS i_src0 i_tgt0 <3= @_sim_itree r S_src S_tgt SS i_src1 i_tgt1.
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
                 exists o_src o_tgt, sim_itree o_src o_tgt w (mrs_src, it_src)
                                               (mrs_tgt, it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (option mname * Any.t -> itree Es Any.t)) := RelProd eq sim_fsem.


  Variant lordC (r: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), Ord.t -> Ord.t -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : Ord.t -> Ord.t -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | lordC_intro
      o_src0 o_src1 o_tgt0 o_tgt1 w st_src st_tgt
      (ORDSRC: Ord.le o_src0 o_src1)
      (ORDTGT: Ord.le o_tgt0 o_tgt1)
      (SIM: r _ _ RR o_src0 o_tgt0 w st_src st_tgt)
    :
      lordC r RR o_src1 o_tgt1 w st_src st_tgt
  .
  Hint Constructors lordC: core.

  Lemma lordC_mon
        r1 r2
        (LE: r1 <8= r2)
    :
      @lordC r1 <8= @lordC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lordC_mon: paco.

  Lemma lordC_compatible: compatible8 (_sim_itree) lordC.
  Proof.
    econs; eauto with paco.
    ii. inv PR. eapply sim_itree_mon_ord; eauto.
    eapply sim_itree_mon; eauto.
    i. econs; eauto; try refl.
  Qed.

  Lemma lordC_spec: lordC <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    intros. gclo. econs.
    { eapply lordC_compatible. }
    ss. eapply lordC_mon; [|eauto]. i. gbase. auto.
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), Ord.t -> Ord.t -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop):
    forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), Ord.t -> Ord.t -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop :=
  | lbindR_intro
      o_src0 o_src1 o_tgt0 o_tgt1 w0 w1

      R_src R_tgt RR
      (st_src0 st_tgt0: st_local)
      (i_src: itree Es R_src) (i_tgt: itree Es R_tgt)
      (SIM: r _ _ RR o_src0 o_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))

      S_src S_tgt SS
      (k_src: ktree Es R_src S_src) (k_tgt: ktree Es R_tgt S_tgt)
      (SIMK: forall st_src1 st_tgt1 vret_src vret_tgt (SIM: RR st_src1 st_tgt1 vret_src vret_tgt), s _ _ SS o_src1 o_tgt1 w1 (st_src1, k_src vret_src) (st_tgt1, k_tgt vret_tgt))
    :
      lbindR r s SS (OrdArith.add o_src1 o_src0) (OrdArith.add o_tgt1 o_tgt0) w1 (st_src0, ITree.bind i_src k_src) (st_tgt0, ITree.bind i_tgt k_tgt)
  .

  Hint Constructors lbindR: core.

  Lemma lbindR_mon
        r1 r2 s1 s2
        (LEr: r1 <8= r2) (LEs: s1 <8= s2)
    :
      lbindR r1 s1 <8= lbindR r2 s2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Definition lbindC r := lbindR r r.
  Hint Unfold lbindC: core.

  Lemma lbindC_wrespectful: wrespectful8 (_sim_itree) lbindC.
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
      { eapply OrdArith.add_base_l. }
      { eapply OrdArith.add_base_l. }
      eapply sim_itree_mon; eauto with paco.
    + rewrite ! bind_bind.
      econs; eauto.
      i. exploit K; eauto. i. des. esplits.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      i. exploit K; eauto. i. des. esplits.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      econs 2; eauto with paco. econs; eauto with paco.
    + rewrite ! bind_bind. des. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      esplits. eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      i. hexploit K; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      econs 2; eauto with paco. econs; eauto with paco.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      i. hexploit K; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. des. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      esplits. eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo8_clo_base. econs; eauto.
  Qed.

  Lemma lbindC_spec: lbindC <9= gupaco8 (_sim_itree) (cpn8 (_sim_itree)).
  Proof.
    intros. eapply wrespect8_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

End SIM.
Hint Resolve sim_itree_mon: paco.


Lemma self_sim_itree `{ns: gnames}:
  forall st itr,
    sim_itree (fun _ '(src, tgt) => src = tgt) top2 (Ord.S Ord.O) (Ord.S Ord.O) tt (st, itr) (st, itr).
Proof.
  pcofix CIH. i. pfold. ides itr.
  { eapply sim_itree_ret; ss. }
  { econs; [eapply Ord.S_lt|]. left. pfold. econs; [eapply Ord.S_lt|]. et. }
  destruct e.
  { dependent destruction c. rewrite <- ! bind_trigger. eapply sim_itree_call; ss.
    ii; subst. esplits. right. eapply CIH.
  }
  destruct s.
  { rewrite <- ! bind_trigger. resub. dependent destruction p.
    { econs; [eapply Ord.S_lt|]. left. pfold. econs; [eapply Ord.S_lt|]. et. }
    { econs; [eapply Ord.S_lt|]. left. pfold. econs; [eapply Ord.S_lt|]. et. }
  }
  { rewrite <- ! bind_trigger. resub. dependent destruction e.
    { econs 10; [eapply Ord.S_lt|]. i. left. pfold. econs 5; [eapply Ord.S_lt|]. et. }
    { econs 6; [eapply Ord.S_lt|]. i. left. pfold. econs 11; [eapply Ord.S_lt|]. et. }
    { econs; et. }
  }
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








Module ModPair.
Section SIMMOD.
   Variable (md_src md_tgt: Mod.t).
   Inductive sim: Prop := mk {
     sim_modsem:
       forall sk
              (SKINCL: Sk.incl md_tgt.(Mod.sk) sk)
              (SKWF: Sk.wf sk),
         <<SIM: ModSemPair.sim (md_src.(Mod.get_modsem) sk) (md_tgt.(Mod.get_modsem) sk)>>;
     sim_sk: <<SIM: md_src.(Mod.sk) = md_tgt.(Mod.sk)>>;
   }.

End SIMMOD.

End ModPair.



Section SIMMOD.

  Context {CONF: EMSConfig}.

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

End SIMMOD.

Section SIMMOD.
   Theorem adequacy_local_strong md_src md_tgt
           (SIM: ModPair.sim md_src md_tgt)
     :
       <<CR: (refines_strong md_tgt md_src)>>
   .
   Proof.
     admit "TODO".
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

   Theorem adequacy_local2 md_src md_tgt
           (SIM: ModPair.sim md_src md_tgt)
     :
       <<CR: (refines2 [md_tgt] [md_src])>>
   .
   Proof.
     eapply ModSem.refines_strong_refines.
     eapply adequacy_local_list_strong. econs; ss.
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
