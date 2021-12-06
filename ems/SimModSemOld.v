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


Lemma self_sim_itree:
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

Lemma self_sim (ms: ModSem.t):
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

Require Import SimGlobalOld.
Require Import Red IRed.

Module TAC.
  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac step := ired_both; gstep; econs; et; [try eapply Ord.S_lt|..].
  Ltac steps := (repeat step); ired_both.
End TAC.
Import TAC.

Section ADEQUACY.
  Section SEMPAIR.
    Variable ms_src: ModSemL.t.
    Variable ms_tgt: ModSemL.t.

    Variable mn: mname.
    Variable world: Type.
    Variable wf: world -> Any.t * Any.t -> Prop.
    Variable le: world -> world -> Prop.

    Hypothesis le_PreOrder: PreOrder le.

    Hypothesis fnsems_find_iff:
      forall fn,
        (<<NONE: alist_find fn ms_src.(ModSemL.fnsems) = None>>) \/
        (exists mn' f,
            (<<MN: mn <> mn'>>) /\
            (<<SRC: alist_find fn ms_src.(ModSemL.fnsems) = Some (transl_all mn' (T:=Any.t) ∘ f)>>) /\
            (<<TGT: alist_find fn ms_tgt.(ModSemL.fnsems) = Some (transl_all mn' (T:=Any.t) ∘ f)>>)) \/
        (exists f_src f_tgt,
            (<<SRC: alist_find fn ms_src.(ModSemL.fnsems) = Some (transl_all mn (T:=Any.t) ∘ f_src)>>) /\
            (<<TGT: alist_find fn ms_tgt.(ModSemL.fnsems) = Some (transl_all mn (T:=Any.t) ∘ f_tgt)>>) /\
            (<<SIM: sim_fsem wf le f_src f_tgt>>)).


    Variant g_lift_rel
            (w0: world) (st_src st_tgt: p_state): Prop :=
    | g_lift_rel_intro
        w1
        (LE: le w0 w1)
        (MN: wf w1 (st_src mn, st_tgt mn))
        (NMN: forall mn' (NIN: mn <> mn'), st_src mn' = st_tgt mn')
    .

    Variant my_r0:
      forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop :=
    | my_r0_intro
        w0
        (itr_src itr_tgt: itree Es Any.t)
        st_src st_tgt o_src o_tgt
        (SIM: sim_itree wf le o_src o_tgt w0 (st_src mn, itr_src) (st_tgt mn, itr_tgt))
        (STATE: forall mn' (MN: mn <> mn'), st_src mn' = st_tgt mn')
      :
        my_r0 (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
                 g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt)
              (Ord.S (4 * o_src))%ord (Ord.S (4 * o_tgt))%ord
              (EventsL.interp_Es (ModSemL.prog ms_src) (transl_all mn itr_src) st_src)
              (EventsL.interp_Es (ModSemL.prog ms_tgt) (transl_all mn itr_tgt) st_tgt)
    .

    Let ord_lemma o0 o1 (LT: (o0 < o1)%ord)
      :
        (Ord.S (Ord.S (Ord.S (4 * o0))) < 4 * o1)%ord.
    Proof.
      eapply Ord.lt_le_lt.
      { eapply Ord.S_lt. }
      transitivity (4 * (Ord.S o0))%ord.
      { rewrite OrdArith.mult_S.
        transitivity (4 * o0 + Ord.S (Ord.S (Ord.S (Ord.S Ord.O))))%ord.
        { rewrite ! OrdArith.add_S. rewrite OrdArith.add_O_r. refl. }
        { eapply OrdArith.le_add_r.
          rewrite ! Ord.from_nat_S. rewrite Ord.from_nat_O. refl. }
      }
      { eapply OrdArith.le_mult_r. eapply Ord.S_supremum. et. }
    Qed.

    Variant my_r1:
      forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop :=
    | my_r1_intro
        mn' w0 st_src st_tgt
        (MN: mn <> mn')
        (SIM: g_lift_rel w0 st_src st_tgt)
        (itr: itree Es Any.t)
      :
        my_r1 (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
                 g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt)
              (Ord.S (Ord.S (Ord.S Ord.O))) (Ord.S (Ord.S (Ord.S Ord.O)))
              (EventsL.interp_Es (ModSemL.prog ms_src) (transl_all mn' itr) st_src)
              (EventsL.interp_Es (ModSemL.prog ms_tgt) (transl_all mn' itr) st_tgt)
    .

    Let my_r := my_r0 \7/ my_r1.
    Let sim_lift: my_r <7= simg.
    Proof.
      ginit.
      { i. eapply cpn7_wcompat; eauto with paco. }
      gcofix CIH. i. destruct PR.
      { destruct H. punfold SIM. inv SIM.
        - rr in RET. des. subst. step. splits; auto. econs; et.
        - hexploit (fnsems_find_iff fn). i. des.
          { steps. rewrite NONE. unfold unwrapU, triggerUB. step. ss. }
          { steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
            guclo bindC_spec. econs.
            { gbase. eapply CIH. right. econs; ss. econs; et. refl. }
            { i. ss. des. destruct vret_src, vret_tgt. des; clarify. inv SIM.
              hexploit K; et. i. des. pclearbot.
              steps. gbase. eapply CIH. left. econs; et.
            }
          }
          { hexploit (SIM (Some mn, varg) (Some mn, varg)); et. i. des.
            steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
            guclo bindC_spec. econs.
            { gbase. eapply CIH. left. econs; ss. et. }
            { i. ss. destruct vret_src, vret_tgt. des; clarify. inv SIM0.
              hexploit K; et. i. des. pclearbot.
              steps. gbase. eapply CIH. left. econs; et.
            }
          }
        - step. i. subst.
          hexploit (K x_tgt). i. des. pclearbot.
          steps. gbase. eapply CIH. left. econs; et.
        - pclearbot. ired_both. gstep. econs.
          { et. }
          { eapply Ord.lt_S. eapply OrdArith.lt_mult_r; et.
            rewrite Ord.from_nat_S. eapply Ord.S_pos. }
          gbase. eapply CIH. left. econs; et.
        - des. pclearbot. ired_both. steps. exists x. steps.
          gbase. eapply CIH. left. econs; et.
        - steps. i. hexploit K. i. pclearbot. steps.
          gbase. eapply CIH. left. econs; et.
        - pclearbot. steps. guclo ordC_spec. econs.
          { refl. }
          { etrans; [|apply Ord.S_le]. refl. }
          gbase. eapply CIH. left. econs; et.
          { unfold update. des_ifs. et. }
          { i. unfold update. des_ifs. et. }
        - pclearbot. steps. guclo ordC_spec. econs.
          { refl. }
          { etrans; [|apply Ord.S_le]. refl. }
          gbase. eapply CIH. left. econs; et.
        - pclearbot. ired_both. gstep. econs.
          { et. }
          { eapply Ord.lt_S. eapply OrdArith.lt_mult_r; et.
            rewrite Ord.from_nat_S. eapply Ord.S_pos. }
          gbase. eapply CIH. left. econs; et.
        - steps. i. hexploit K. i. pclearbot. steps.
          gbase. eapply CIH. left. econs; et.
        - des. pclearbot. steps. exists x. steps.
          gbase. eapply CIH. left. econs; et.
        - pclearbot. steps. guclo ordC_spec. econs.
          { etrans; [|apply Ord.S_le]. refl. }
          { refl. }
          gbase. eapply CIH. left. econs; et.
          { unfold update. des_ifs. et. }
          { i. unfold update. des_ifs. et. }
        - pclearbot. steps. guclo ordC_spec. econs.
          { etrans; [|apply Ord.S_le]. refl. }
          { refl. }
          gbase. eapply CIH. left. econs; et.
      }
      { destruct H. ides itr.
        { steps. gstep. econs. esplits; et. }
        { steps. gbase. eapply CIH. right. econs; et. }
        rewrite <- ! bind_trigger. destruct e.
        { resub. destruct c. hexploit (fnsems_find_iff fn). i. des.
          { steps. rewrite NONE. unfold unwrapU, triggerUB. step. ss. }
          { inv SIM. steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
            guclo bindC_spec. econs.
            { gbase. eapply CIH. right. econs; ss. econs; et. }
            { i. ss. des. destruct vret_src, vret_tgt. des; clarify.
              steps. gbase. eapply CIH. right. econs; et. }
          }
          { inv SIM. hexploit (SIM0 (Some mn', args) (Some mn', args)); et. i. des.
            steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
            guclo bindC_spec. econs.
            { gbase. eapply CIH. left. econs; ss. et. }
            { i. ss. destruct vret_src, vret_tgt. des; clarify.
              steps. gbase. eapply CIH. right. econs; et.
              inv SIM. econs.
              { etrans; et. }
              { et. }
              { et. }
            }
          }
        }
        destruct s.
        { resub. destruct p.
          { steps. gbase. eapply CIH. right. econs; et.
            inv SIM. econs; et.
            { unfold update. des_ifs. }
            { ii. unfold update. des_ifs. et. }
          }
          { steps. gbase. eapply CIH. right.
            replace (st_tgt mn') with (st_src mn'); et.
            { econs; et. }
            { inv SIM. et. }
          }
        }
        { resub. destruct e.
          { ired_both. gstep. eapply simg_chooseR; et.
            { eapply Ord.S_lt. }
            i. gstep. eapply simg_chooseL; et.
            { eapply Ord.S_lt. }
            exists x. steps.
            gbase. eapply CIH; et. right. econs; et.
          }
          { ired_both. gstep. eapply simg_takeL; et.
            { eapply Ord.S_lt. }
            i. gstep. eapply simg_takeR; et.
            { eapply Ord.S_lt. }
            exists x. steps.
            gbase. eapply CIH; et. right. econs; et.
          }
          { steps. i. subst. steps.
            gbase. eapply CIH; et. right. econs; et. }
        }
      }
      Unshelve. all: try exact 0.
    Qed.

    Context `{CONF: EMSConfig}.

    Hypothesis INIT:
      exists w, g_lift_rel w (ModSemL.initial_p_state ms_src) (ModSemL.initial_p_state ms_tgt).

    Lemma adequacy_local_aux (P Q: Prop)
          (WF: Q -> P)
      :
        (Beh.of_program (ModSemL.compile ms_tgt (Some P)))
        <1=
        (Beh.of_program (ModSemL.compile ms_src (Some Q))).
    Proof.
      eapply adequacy_global_itree; ss.
      hexploit INIT. i. des.
      eexists _, _. ginit.
      { eapply cpn7_wcompat; eauto with paco. }
      unfold ModSemL.initial_itr, assume.
      hexploit (fnsems_find_iff "main"). i. des.
      { steps. unshelve esplits; et. unfold ITree.map, unwrapU, triggerUB. steps.
        rewrite NONE. steps. ss. }
      { steps. unshelve esplits; et. unfold ITree.map, unwrapU. steps.
        rewrite SRC. rewrite TGT. steps. guclo bindC_spec. econs.
        { gfinal. right. eapply sim_lift. right. econs; et. }
        { i. destruct vret_src, vret_tgt. des; clarify. steps.
          gstep. econs; et. }
      }
      { inv H. hexploit (SIM (None, initial_arg) (None, initial_arg)); et. i. des.
        steps. unshelve esplits; et. unfold ITree.map, unwrapU. steps.
        rewrite SRC. rewrite TGT. steps. guclo bindC_spec. econs.
        { gfinal. right. eapply sim_lift. left. econs; et. }
        { i. destruct vret_src, vret_tgt. des; clarify. steps.
          gstep. econs; et. }
      }
      Unshelve. all: try exact 0.
    Qed.
  End SEMPAIR.

  Theorem adequacy_local_strong md_src md_tgt
          (SIM: ModPair.sim md_src md_tgt)
    :
      <<CR: (refines_strong md_tgt md_src)>>
  .
  Proof.
    ii. unfold ModL.compile, ModL.enclose in *.
    destruct (classic (ModL.wf (ModL.add (Mod.add_list ctx) md_src))).
    2:{ eapply ModSemL.compile_not_wf. ss. }
    pose (sk_tgt := (ModL.sk (ModL.add (Mod.add_list ctx) md_tgt))).
    pose (sk_src := (ModL.sk (ModL.add (Mod.add_list ctx) md_src))).
    assert (SKEQ: sk_tgt = sk_src).
    { unfold sk_src, sk_tgt. ss. f_equal.
      inv SIM. auto. }
    rr in H. unfold ModL.enclose in *. fold sk_src in H. des. inv WF.
    rename SK into SKWF.
    rename wf_fnsems into FNWF.
    rename wf_initial_mrs into MNWF.
    inv SIM. hexploit (sim_modsem (Sk.canon sk_tgt)).
    { etrans; [|eapply Sk.sort_incl]. ss. ii. eapply in_or_app. auto. }
    { ss. fold sk_src in SKWF. rewrite SKEQ. clear - SKWF.
      unfold Sk.wf in *. ss. eapply Permutation.Permutation_NoDup; [|et].
      eapply Permutation.Permutation_map. eapply Sk.SkSort.sort_permutation. }
    i. inv H. des.
    assert (WFTGT: ModL.wf (ModL.add (Mod.add_list ctx) md_tgt)).
    { rr. unfold ModL.enclose. fold sk_src sk_tgt.
      rewrite SKEQ in *. split; auto. econs.
      { clear MNWF.
        match goal with
        | H: NoDup ?l0 |- NoDup ?l1 => replace l1 with l0
        end; auto. ss.
        rewrite ! List.map_app. f_equal. rewrite ! List.map_map.
        eapply Forall2_eq. eapply Forall2_apply_Forall2; et.
        i. destruct a, b. inv H. ss.
      }
      { clear FNWF.
        match goal with
        | H: NoDup ?l0 |- NoDup ?l1 => replace l1 with l0
        end; auto. ss.
        rewrite ! List.map_app. f_equal. ss.
        rewrite sim_mn. auto.
      }
    }
    eapply adequacy_local_aux in PR; et.
    { ss. ii. fold sk_src sk_tgt. rewrite <- SKEQ. rewrite ! alist_find_app_o. des_ifs.
      { eapply alist_find_some in Heq.
        rewrite Mod.add_list_fnsems in Heq.
        rewrite <- fold_right_app_flat_map in Heq. ss.
        eapply in_flat_map in Heq. des.
        eapply in_map_iff in Heq0. des. destruct x1. ss. clarify.
        right. left. esplits; et.
        instantiate (1:=ModSem.mn (Mod.get_modsem md_src (Sk.sort sk_tgt))).
        ii. eapply NoDup_app_disjoint.
        { rewrite List.map_app in MNWF. eapply MNWF. }
        { rewrite Mod.add_list_initial_mrs.
          rewrite <- fold_right_app_flat_map. eapply in_map.
          eapply in_flat_map. ss. esplits; et. }
        { ss. rewrite <- SKEQ. rewrite H. auto. }
      }
      { rewrite ! alist_find_map_snd. uo. des_ifs_safe ltac:(auto).
        eapply alist_find_some in Heq0. right. right.
        eapply Forall2_In_l in sim_fnsems; et. des. inv sim_fnsems0.
        destruct b. esplits; et. erewrite alist_find_some_iff; et.
        { rewrite sim_mn. et. }
        { inv WFTGT. inv H1. ss. rewrite List.map_app in wf_fnsems.
          apply nodup_app_r in wf_fnsems.
          rewrite List.map_map in wf_fnsems. ss. fold sk_tgt in wf_fnsems.
          erewrite List.map_ext; et. i. destruct a. ss.
        }
        { ss. inv H. ss. clarify. }
      }
    }
    { exists w_init. econs.
      { refl. }
      { unfold ModSemL.initial_p_state.
        erewrite ! alist_find_some_iff; et.
        { clear FNWF.
          match goal with
          | H: NoDup ?l0 |- NoDup ?l1 => replace l1 with l0
          end; auto. ss.
          fold sk_src. fold sk_tgt. rewrite <- SKEQ.
          rewrite ! List.map_app. f_equal. ss. f_equal. auto.
        }
        { ss. eapply in_or_app. right. ss. left. fold sk_tgt. f_equal. auto. }
        { ss. eapply in_or_app. right. ss. left. fold sk_src. rewrite SKEQ. auto. }
      }
      { ii. ss. fold sk_src sk_tgt. rewrite SKEQ. unfold ModSemL.initial_p_state.
        ss. rewrite ! alist_find_app_o. des_ifs_safe.
        rewrite <- SKEQ. ss. rewrite ! eq_rel_dec_correct. des_ifs. }
    }
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

End ADEQUACY.
