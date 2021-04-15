Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
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

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.







Print function_Map. (*** TODO: use Dec. Move to proper place ***)

Global Instance Dec_RelDec K `{Dec K}: @RelDec K eq :=
  { rel_dec := dec }.

Global Instance Dec_RelDec_Correct K `{Dec K}: RelDec_Correct Dec_RelDec.
Proof.
  unfold Dec_RelDec. ss.
  econs. ii. ss. unfold Dec_RelDec. split; ii.
  - unfold rel_dec in *. unfold sumbool_to_bool in *. des_ifs.
  - unfold rel_dec in *. unfold sumbool_to_bool in *. des_ifs.
Qed.






Section SIM.

  Context `{Σ: GRA.t}.

  Let st_local: Type := (Σ * Any.t * Σ).

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).
  Variable wf: W -> Prop.

  Variant _sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), Ord.t -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : Ord.t -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_ret
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      (WF: wf (mrs_src0, mrs_tgt0))
      v_src v_tgt
      (RET: RR (mrs_src0, fr_src0) (mrs_tgt0, fr_tgt0) v_src v_tgt)
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), (Ret v_src)) ((mrs_tgt0, fr_tgt0), (Ret v_tgt))
  | sim_itree_tau
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (K: sim_itree _ _ RR i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 (st_src0, tau;; i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_call
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      fn varg k_src k_tgt
      (WF: wf (mrs_src0, mrs_tgt0))
      (K: forall vret mrs_src1 mrs_tgt1 (WF: wf (mrs_src1, mrs_tgt1)),
          exists i1, sim_itree _ _ RR i1 ((mrs_src1, fr_src0), k_src vret) ((mrs_tgt1, fr_tgt0), k_tgt vret))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Call fn varg) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Call fn varg) >>= k_tgt)
  | sim_itree_syscall
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          exists i1, sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src vret) ((mrs_tgt0, fr_tgt0), k_tgt vret))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Syscall fn varg rvs) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Syscall fn varg rvs) >>= k_tgt)
  (*** TODO: sim_syscall is nontrivial; it should accept "injected" memory... ***)
  (*** TODO: simplify the model: Syscall: list val -> val ***)

  | sim_itree_choose_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      X_src X_tgt k_src k_tgt
      (K: forall (x_tgt: X_tgt), exists (x_src: X_src) i1, sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src x_src) ((mrs_tgt0, fr_tgt0), k_tgt x_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Choose X_src) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Choose X_tgt) >>= k_tgt)
  | sim_itree_take_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      X_src X_tgt k_src k_tgt
      (K: forall (x_src: X_src), exists (x_tgt: X_tgt) i1, sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src x_src) ((mrs_tgt0, fr_tgt0), k_tgt x_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Take X_src) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Take X_tgt) >>= k_tgt)
  | sim_itree_pput_both
      i0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mr_src0 mr_tgt0 mp_src1 mp_tgt1 mp_src0 mp_tgt0
      (K: sim_itree _ _ RR i1 ((mr_src0, mp_src1, fr_src0), k_src tt) ((mr_tgt0, mp_tgt1, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 ((mr_src0, mp_src0, fr_src0), trigger (PPut mp_src1) >>= k_src)
                 ((mr_tgt0, mp_tgt0, fr_tgt0), trigger (PPut mp_tgt1) >>= k_tgt)
  | sim_itree_mput_both
      i0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mr_src0 mr_tgt0 mr_src1 mr_tgt1 mp_src0 mp_tgt0
      (K: sim_itree _ _ RR i1 ((mr_src1, mp_src0, fr_src0), k_src tt) ((mr_tgt1, mp_tgt0, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 ((mr_src0, mp_src0, fr_src0), trigger (MPut mr_src1) >>= k_src)
                 ((mr_tgt0, mp_tgt0, fr_tgt0), trigger (MPut mr_tgt1) >>= k_tgt)
  | sim_itree_fput_both
      i0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mr_src0 mr_tgt0 fr_src1 fr_tgt1 mp_src0 mp_tgt0
      (K: sim_itree _ _ RR i1 ((mr_src0, mp_src0, fr_src1), k_src tt) ((mr_tgt0, mp_tgt0, fr_tgt1), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 ((mr_src0, mp_src0, fr_src0), trigger (FPut fr_src1) >>= k_src)
                 ((mr_tgt0, mp_tgt0, fr_tgt0), trigger (FPut fr_tgt1) >>= k_tgt)
  | sim_itree_pget_both
      i0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mr_src0 mr_tgt0 mp_src0 mp_tgt0
      (K: sim_itree _ _ RR i1 ((mr_src0, mp_src0, fr_src0), k_src mp_src0) ((mr_tgt0, mp_tgt0, fr_tgt0), k_tgt mp_tgt0))
    :
      _sim_itree sim_itree RR i0 ((mr_src0, mp_src0, fr_src0), trigger (PGet) >>= k_src)
                 ((mr_tgt0, mp_tgt0, fr_tgt0), trigger (PGet) >>= k_tgt)
  | sim_itree_mget_both
      i0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mr_src0 mr_tgt0 mp_src0 mp_tgt0
      (K: sim_itree _ _ RR i1 ((mr_src0, mp_src0, fr_src0), k_src mr_src0) ((mr_tgt0, mp_tgt0, fr_tgt0), k_tgt mr_tgt0))
    :
      _sim_itree sim_itree RR i0 ((mr_src0, mp_src0, fr_src0), trigger (MGet) >>= k_src)
                 ((mr_tgt0, mp_tgt0, fr_tgt0), trigger (MGet) >>= k_tgt)
  | sim_itree_fget_both
      i0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mr_src0 mr_tgt0 mp_src0 mp_tgt0
      (K: sim_itree _ _ RR i1 ((mr_src0, mp_src0, fr_src0), k_src fr_src0) ((mr_tgt0, mp_tgt0, fr_tgt0), k_tgt fr_tgt0))
    :
      _sim_itree sim_itree RR i0 ((mr_src0, mp_src0, fr_src0), trigger (FGet) >>= k_src)
                 ((mr_tgt0, mp_tgt0, fr_tgt0), trigger (FGet) >>= k_tgt)



  | sim_itree_tau_src
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_choose_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: exists (x: X), sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src x) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Choose X) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_take_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: forall (x: X), sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src x) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Take X) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)

  | sim_itree_pput_src
      i0 st_tgt0 fr_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mr0 mp1 mp0
      (K: sim_itree _ _ RR i1 ((mr0, mp1, fr_src0), k_src tt) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mr0, mp0, fr_src0), trigger (PPut mp1) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itree_mput_src
      i0 st_tgt0 fr_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mr0 mr1 mp0
      (K: sim_itree _ _ RR i1 ((mr1, mp0, fr_src0), k_src tt) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mr0, mp0, fr_src0), trigger (MPut mr1) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itree_fput_src
      i0 mrs_src0 st_tgt0 fr_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      fr_src1
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src1), k_src tt) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (FPut fr_src1) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_pget_src
      i0 st_tgt0 fr_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mr0 mp0
      (K: sim_itree _ _ RR i1 ((mr0, mp0, fr_src0), k_src mp0) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mr0, mp0, fr_src0), trigger (PGet) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itree_mget_src
      i0 fr_src0 st_tgt0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mr0 mp0
      (K: sim_itree _ _ RR i1 ((mr0, mp0, fr_src0), k_src mr0) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mr0, mp0, fr_src0), trigger (MGet) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itree_fget_src
      i0 mrs_src0 st_tgt0 fr_src0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src fr_src0) ((st_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (FGet) >>= k_src)
                 (st_tgt0, i_tgt)






  | sim_itree_tau_tgt
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_choose_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X i_src k_tgt
      (ORD: Ord.lt i1 i0)
      (K: forall (x: X), sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt x))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Choose X) >>= k_tgt)
  | sim_itree_take_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X i_src k_tgt
      (ORD: Ord.lt i1 i0)
      (K: exists (x: X), sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt x))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Take X) >>= k_tgt)

  | sim_itree_pput_tgt
      i0 st_src0 fr_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      mr0 mp1 mp0
      (K: sim_itree _ _ RR i1 (st_src0, i_src) ((mr0, mp1, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 (st_src0, i_src)
                 ((mr0, mp0, fr_tgt0), trigger (PPut mp1) >>= k_tgt)
  | sim_itree_mput_tgt
      i0 st_src0 fr_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      mr0 mr1 mp0
      (K: sim_itree _ _ RR i1 (st_src0, i_src) ((mr1, mp0, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 (st_src0, i_src)
                 ((mr0, mp0, fr_tgt0), trigger (MPut mr1) >>= k_tgt)
  | sim_itree_fput_tgt
      i0 mrs_tgt0 st_src0 fr_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      fr_tgt1
      (K: sim_itree _ _ RR i1 (st_src0, i_src) ((mrs_tgt0, fr_tgt1), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 (st_src0, i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FPut fr_tgt1) >>= k_tgt)

  | sim_itree_pget_tgt
      i0 st_src0 fr_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      mr0 mp0
      (K: sim_itree _ _ RR i1 (st_src0, i_src) ((mr0, mp0, fr_tgt0), k_tgt mp0))
    :
      _sim_itree sim_itree RR i0 (st_src0, i_src)
                 ((mr0, mp0, fr_tgt0), trigger (PGet) >>= k_tgt)
  | sim_itree_mget_tgt
      i0 fr_tgt0 st_src0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      mr0 mp0
      (K: sim_itree _ _ RR i1 (st_src0, i_src) ((mr0, mp0, fr_tgt0), k_tgt mr0))
    :
      _sim_itree sim_itree RR i0 (st_src0, i_src)
                 ((mr0, mp0, fr_tgt0), trigger (MGet) >>= k_tgt)
  | sim_itree_fget_tgt
      i0 mrs_tgt0 st_src0 fr_tgt0
      i1 k_tgt i_src
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 ((st_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt fr_tgt0))
    :
      _sim_itree sim_itree RR i0 (st_src0, i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FGet) >>= k_tgt)
  .

  Definition sim_itree: _ -> relation _ :=
    paco6 _sim_itree bot6 _ _ (fun _ _ => @eq Any.t).

  Lemma sim_itree_mon: monotone6 _sim_itree.
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

  Lemma sim_itree_mon_ord r S_src S_tgt SS i0 i1 (ORD: (i0 <= i1)%ord): @_sim_itree r S_src S_tgt SS i0 <2= @_sim_itree r S_src S_tgt SS i1.
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
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
  Qed.

  Definition sim_fsem: relation (Any.t -> itree Es Any.t) :=
    (eq ==> (fun it_src it_tgt => forall mrs_src mrs_tgt (SIMMRS: wf (mrs_src, mrs_tgt)),
                 exists n, sim_itree n ((mrs_src, URA.unit), it_src)
                                     ((mrs_tgt, URA.unit), it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (Any.t -> itree Es Any.t)) := RelProd eq sim_fsem.


  Variant lordC (r: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), Ord.t -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : Ord.t -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | lordC_intro
      o0 o1 st_src st_tgt
      (ORD: Ord.le o0 o1)
      (SIM: r _ _ RR o0 st_src st_tgt)
    :
      lordC r RR o1 st_src st_tgt
  .
  Hint Constructors lordC: core.

  Lemma lordC_mon
        r1 r2
        (LE: r1 <6= r2)
    :
      @lordC r1 <6= @lordC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lordC_mon: paco.

  Lemma lordC_compatible: compatible6 (_sim_itree) lordC.
  Proof.
    econs; eauto with paco.
    ii. inv PR. eapply sim_itree_mon_ord; eauto.
    eapply sim_itree_mon; eauto.
    i. econs; eauto. refl.
  Qed.

  Lemma lordC_spec: lordC <7= gupaco6 (_sim_itree) (cpn6 _sim_itree).
  Proof.
    intros. gclo. econs.
    { eapply lordC_compatible. }
    ss. eapply lordC_mon; [|eauto]. i. gbase. auto.
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), Ord.t -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop):
    forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), Ord.t -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop :=
  | lbindR_intro
      o0 o1

      R_src R_tgt RR
      (st_src0 st_tgt0: st_local)
      (i_src: itree Es R_src) (i_tgt: itree Es R_tgt)
      (SIM: r _ _ RR o0 (st_src0, i_src) (st_tgt0, i_tgt))

      S_src S_tgt SS
      (k_src: ktree Es R_src S_src) (k_tgt: ktree Es R_tgt S_tgt)
      (SIMK: forall st_src1 st_tgt1 vret_src vret_tgt (SIM: RR st_src1 st_tgt1 vret_src vret_tgt), s _ _ SS o1 (st_src1, k_src vret_src) (st_tgt1, k_tgt vret_tgt))
    :
      lbindR r s SS (OrdArith.add o1 o0) (st_src0, ITree.bind i_src k_src) (st_tgt0, ITree.bind i_tgt k_tgt)
  .

  Hint Constructors lbindR: core.

  Lemma lbindR_mon
        r1 r2 s1 s2
        (LEr: r1 <6= r2) (LEs: s1 <6= s2)
    :
      lbindR r1 s1 <6= lbindR r2 s2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Definition lbindC r := lbindR r r.
  Hint Unfold lbindC: core.

  Lemma lbindC_wrespectful: wrespectful6 (_sim_itree) lbindC.
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
    + rewrite ! bind_bind. econs; eauto.
      i. exploit K; eauto. i. des. eexists.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      i. exploit K; eauto. i. des. eexists.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      i. exploit K; eauto. i. des. esplits.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      i. exploit K; eauto. i. des. esplits.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      econs 2; eauto with paco. econs; eauto with paco.
    + rewrite ! bind_bind. des. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eexists. eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      i. hexploit K; eauto. i.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      econs 2; eauto with paco. econs; eauto with paco.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      i. hexploit K; eauto. i.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. des. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eexists. eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
  Qed.

  Lemma lbindC_spec: lbindC <7= gupaco6 (_sim_itree) (cpn6 (_sim_itree)).
  Proof.
    intros. eapply wrespect6_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

End SIM.
Hint Resolve sim_itree_mon: paco.


Lemma self_sim_itree `{Σ: GRA.t}:
  forall n mr st fr itr,
    sim_itree (fun '(src, tgt) => src = tgt) n (mr, st, fr, itr) (mr, st, fr, itr).
Proof.
  pcofix CIH. i. pfold. ides itr.
  { eapply sim_itree_ret; ss. }
  { eapply sim_itree_tau. right. eapply CIH; ss. }
  destruct e.
  { dependent destruction c. rewrite <- ! bind_trigger. eapply sim_itree_call; ss.
    ii; subst. exists 0. right. destruct mrs_tgt1. eapply CIH.
  }
  destruct s.
  { rewrite <- ! bind_trigger. dependent destruction r0; econs; eauto. }
  destruct s.
  { rewrite <- ! bind_trigger. dependent destruction p; econs; eauto. }
  { rewrite <- ! bind_trigger. dependent destruction e; econs; eauto. }
Unshelve.
  all: try (exact 0).
Qed.



(*** Q: do we need SimMemOh.le (and lepriv) ??? ***)

(*** Let's say that le/lepriv can be encoded using RA and CheckWf... ***)
(*** Q: Is "Source CheckWf >= Target CheckWf" trivial? or can be derived automatically? ***)
(*** A: I think no. It looks like a real user obligation. ***)
(*** N.B.: In the course of verifying "Source CheckWf >= Target CheckWf", one may need "le".
         For an instance, if target RA is in some sense monotonic, while source RA is unit,
         we have to prove that "Target CheckWf" holds from the ground. To do so, we need "le".
         I am not entirely sure that we don't need "lepriv",
         but (1) lepriv alone won't scale with concurrency,
         so we need separation (putting into/out of function local resource), then
         (2) it seems function-local resource (without lepriv) is sufficient for the cases
         that I can think of ***)

(*** desiderata: (1) state-aware simulation relation !!!! ***)
(*** (2) not whole function frame, just my function frame !!!! ***)
(*** (3) would be great if induction tactic works !!!! (study itree case study more) ***)



Module ModSemPair.
Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Variable (ms_src ms_tgt: ModSem.t).

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).
  Inductive sim: Prop := mk {
    wf: W -> Prop;
    sim_fnsems: Forall2 (sim_fnsem wf) ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems);
    sim_mn: ms_src.(ModSem.mn) = ms_tgt.(ModSem.mn);
    sim_initial: wf ((ms_src.(ModSem.initial_mr), ms_src.(ModSem.initial_st)), (ms_tgt.(ModSem.initial_mr), ms_tgt.(ModSem.initial_st)));
  }.

End SIMMODSEM.

Lemma self_sim_mod `{Σ: GRA.t} (ms: ModSem.t) (WF: ModSem.wf ms):
  sim ms ms.
Proof.
  econs; et.
  - instantiate (1:=(fun '(src, tgt) => src = tgt)). (* fun p => fst p = snd p *)
    revert WF. generalize (ModSem.fnsems ms).
    induction l; ii; ss.
    econs; eauto. econs; ss. ii; clarify. destruct mrs_tgt. exploit self_sim_itree; et.
  - ss.
Unshelve.
all: try (exact 0).
Qed.

End ModSemPair.

Require Import SimModSemL.





Section ADQ.

  Context `{Σ: GRA.t}.

  Variable ms_src ms_tgt: ModSem.t.

  Let wf_lift (wf: ((Σ * Any.t) * (Σ * Any.t) -> Prop)): (alist string (Σ * Any.t) * alist string (Σ * Any.t) -> Prop) :=
    (fun '(mrs_src, mrs_tgt) =>
       exists mr_src mp_src mr_tgt mp_tgt,
         (<<SRC: mrs_src = Maps.add ms_src.(ModSem.mn) (mr_src, mp_src) Maps.empty>>) /\
         (<<TGT: mrs_tgt = Maps.add ms_tgt.(ModSem.mn) (mr_tgt, mp_tgt) Maps.empty>>) /\
         (<<WF: wf ((mr_src, mp_src), (mr_tgt, mp_tgt))>>)
    )
  .

  Lemma adequacy_lift_itree
        wf
        n mr_src0 mp_src0 fr_src0 i_src0 mr_tgt0 mp_tgt0 fr_tgt0 i_tgt0
        (MN: ms_src.(ModSem.mn) = ms_tgt.(ModSem.mn))
        (SIM: SimModSem.sim_itree wf n (mr_src0, mp_src0, fr_src0, i_src0) (mr_tgt0, mp_tgt0, fr_tgt0, i_tgt0))
    :
      <<SIM: sim_itree (wf_lift wf) (2 * n)%ord ([(ModSem.mn ms_src, (mr_src0, mp_src0))], fr_src0, transl_all (ModSem.mn ms_src) i_src0)
                       ([(ModSem.mn ms_tgt, (mr_tgt0, mp_tgt0))], fr_tgt0, transl_all (ModSem.mn ms_tgt) i_tgt0)>>
  .
  Proof.
    r. ginit.
    { eapply cpn6_wcompat. eauto with paco. }
    revert_until wf. gcofix CIH. i.
    punfold SIM. dependent destruction SIM.
    - unfold transl_all. rewrite ! unfold_interp. ss. gstep. econs; eauto.
      ss. esplits; ss.
    - unfold transl_all. rewrite ! unfold_interp. ss. gstep. econs; eauto.
      pclearbot. gbase. eapply CIH; et.
    - unfold transl_all. rewrite ! interp_bind. rewrite ! unfold_interp. ss. rewrite ! bind_bind.
      replace (trigger EventsL.PushFrame;; r1 <- trigger (Call fn varg);; x <- (trigger EventsL.PopFrame;; Ret r1);;
               x0 <- (tau;; interp (handle_all (ModSem.mn ms_src)) (Ret x));; interp (handle_all (ModSem.mn ms_src)) (k_src x0)) with
          (trigger EventsL.PushFrame;; r <- trigger (Call fn varg);; trigger EventsL.PopFrame;; tau;; (interp (handle_all (ModSem.mn ms_src)) (k_src r))); cycle 1.
      { grind. }
      replace (trigger EventsL.PushFrame;; r1 <- trigger (Call fn varg);; x <- (trigger EventsL.PopFrame;; Ret r1);;
               x0 <- (tau;; interp (handle_all (ModSem.mn ms_tgt)) (Ret x));; interp (handle_all (ModSem.mn ms_tgt)) (k_tgt x0)) with
          (trigger EventsL.PushFrame;; r <- trigger (Call fn varg);; trigger EventsL.PopFrame;; tau;; (interp (handle_all (ModSem.mn ms_tgt)) (k_tgt r))); cycle 1.
      { grind. }
      gstep. econs; eauto.
      { rr. esplits; ss. }
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
      match goal with | [ |- r _ _ _ _ ?x _ ] => remember x as tmp end.
      rewrite MN. subst tmp.
      eapply CIH; et.
    - unfold transl_all. rewrite ! unfold_interp. ired.
      rewrite <- MN. gstep. econs; ss; et.
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      unfold alist_add; ss. des_ifs.
      { bsimpl. unfold rel_dec in *. ss. des_sumbool; ss. }
      ired. gstep; econs; et. pclearbot. gbase.
      match goal with | [ |- r _ _ _ _ ?x _ ] => remember x as tmp end.
      rewrite MN. subst tmp.
      eapply CIH; et.
    - unfold transl_all. rewrite ! unfold_interp. ired.
      gstep. econs; et. pclearbot. ired. gstep. econs; et. gbase. eapply CIH; et.
    - unfold transl_all. rewrite ! unfold_interp. ired.
      rewrite <- MN. gstep. econs; ss; et.
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      ired. gstep; econs; et. pclearbot. gbase.
      match goal with | [ |- r _ _ _ _ ?x _ ] => remember x as tmp end.
      rewrite MN. subst tmp.
      eapply CIH; et.
    - unfold transl_all. rewrite ! unfold_interp. ired.
      rewrite <- MN. gstep. econs; ss; et.
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      { unfold rel_dec. ss. des_ifs. des_sumbool; ss. }
      ired. gstep; econs; et. pclearbot. gbase.
      match goal with | [ |- r _ _ _ _ ?x _ ] => remember x as tmp end.
      rewrite MN. subst tmp.
      eapply CIH; et.
    - unfold transl_all. rewrite ! unfold_interp. ired.
      gstep. econs; et. pclearbot. ired. gstep. econs; et. gbase. eapply CIH; et.
    (* - unfold transl_all. ired. *)
    (*   gstep. econs; et. *)
    (*   { instantiate (1:=(2 * i1 + 1)%ord). eapply Ord.S_is_S in ORD. eapply Ord.lt_le_lt; cycle 1. *)
    (*     { rewrite <- ORD. refl. } *)
    (*     assert(T: ((Ord.S i1) == (i1 + 1))%ord). *)
    (*     { rewrite Ord.from_nat_S. rewrite OrdArith.add_S. ss. rewrite OrdArith.add_O_r. refl. } *)
    (*     rewrite T. rewrite OrdArith.mult_dist. *)
    (*     rewrite OrdArith.mult_1_r. *)
    (*     eapply OrdArith.lt_add_r. eapply OrdArith.lt_from_nat. lia. *)
    (*   } *)
    (*   gstep. econs; et. *)


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
      gstep. econs; ss; et.
      { eapply OrdArith.add_lt_l. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
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
      gstep. econs; ss; et.
      { eapply OrdArith.add_lt_l. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      ired. gbase. eapply CIH; et.


    (***** TGT *****)
    - unfold transl_all. match goal with | [ |- gpaco6 _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
      rewrite unfold_interp. ired. subst.
      gstep. econs; et.
      { eapply OrdArith.lt_mult_r; et. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      pclearbot.
      gbase. eapply CIH; et.
    - unfold transl_all. match goal with | [ |- gpaco6 _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
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
    - unfold transl_all. match goal with | [ |- gpaco6 _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
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
    - unfold transl_all. match goal with | [ |- gpaco6 _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
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
    - unfold transl_all. match goal with | [ |- gpaco6 _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
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
    - unfold transl_all. match goal with | [ |- gpaco6 _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
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
      gstep. econs; ss; et.
      { eapply OrdArith.add_lt_l. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      ired. gbase. eapply CIH; et.
    - unfold transl_all. match goal with | [ |- gpaco6 _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
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
    - unfold transl_all. match goal with | [ |- gpaco6 _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
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
    - unfold transl_all. match goal with | [ |- gpaco6 _ _ _ _ _ _ _ _ ?x _ ] => remember x as tmp end.
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
      gstep. econs; ss; et.
      { eapply OrdArith.add_lt_l. rewrite <- Ord.from_nat_O. eapply OrdArith.lt_from_nat. lia. }
      ired. gbase. eapply CIH; et.
  Unshelve.
    all: exact 0.
  Qed.

  Lemma adequacy_lift_fsem
        wf f_src f_tgt
        (MN: ms_src.(ModSem.mn) = ms_tgt.(ModSem.mn))
        (SIM: SimModSem.sim_fsem wf f_src f_tgt)
    :
      sim_fsem (wf_lift wf) (fun args => transl_all ms_src.(ModSem.mn) (f_src args))
               (fun args => transl_all ms_tgt.(ModSem.mn) (f_tgt args))
  .
  Proof.
    ii. clarify. rr in SIM. specialize (SIM y y eq_refl).
    r in SIMMRS. des. ss. subst. unfold alist_add in *. ss. clarify.
    specialize (SIM (mr_src, mp_src) (mr_tgt, mp_tgt)).
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
    econs; eauto.
    { instantiate (1:=top2). ss. }
    { instantiate (1:=wf_lift wf).
      ss.
      eapply Forall2_apply_Forall2; et.
      i. destruct a, b; ss. rr in H. des; ss. rr in H. r in H0. ss. clarify.
      split; ss. r. ss.
      eapply adequacy_lift_fsem; et.
    }
    ss. esplits; ss; et.
  Qed.

End ADQ.




Module ModPair.
Section SIMMOD.
   Context `{Σ: GRA.t}.
   Variable (md_src md_tgt: Mod.t).
   Inductive sim: Prop := mk {
     sim_modsem:
       forall skenv 
              (SKINCL: Sk.incl md_tgt.(Mod.sk) skenv)
              (SKWF: SkEnv.wf skenv), <<SIM: ModSemLPair.sim (md_src.(Mod.get_modsem) skenv) (md_tgt.(Mod.get_modsem) skenv)>>;
     sim_sk: <<SIM: md_src.(Mod.sk) = md_tgt.(Mod.sk)>>;
     sim_wf:
       forall skenv (WF: ModSemL.wf (md_src.(Mod.get_modsem) skenv)), <<WF: ModSemL.wf (md_tgt.(Mod.get_modsem) skenv)>>;
   }.

End SIMMOD.
End ModPair.

Section ADQ.
  Context `{Σ: GRA.t}.
  Variable md_src md_tgt: Mod.t.
  Theorem adequacy_lift_mod
          (SIM: ModPair.sim md_src md_tgt)
    :
      <<SIM: ModLPair.sim md_src md_tgt>>
  .
  Proof.
    inv SIM.
    econs; eauto.
    admit "Fix ModSemLPair".
  Qed.

End ADQ.



Section SIMMOD.
   Context `{Σ: GRA.t}.

   Definition refines (md_tgt md_src: ModL.t): Prop :=
     (* forall (ctx: list Mod.t), Beh.of_program (ModL.compile (add_list (md_tgt :: ctx))) <1= *)
     (*                           Beh.of_program (ModL.compile (add_list (md_src :: ctx))) *)
     forall (ctx: list Mod.t), Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) md_tgt)) <1=
                               Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) md_src))
   .

   (*** vertical composition ***)
   Global Program Instance refines_PreOrder: PreOrder refines.
   Next Obligation. ii. ss. Qed.
   Next Obligation. ii. eapply H0. eapply H. ss. Qed.

   (*** horizontal composition ***)
   Theorem refines_add
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines md0_tgt md0_src)
         (SIM1: refines md1_tgt md1_src)
     :
       <<SIM: refines (ModL.add md0_tgt md1_tgt) (ModL.add md0_src md1_src)>>
   .
   Proof.
     ii. r in SIM0. r in SIM1.
     (***
ctx (a0 b0)
(ctx a0) b0
(ctx a0) b1
      ***)
     rewrite ModL.add_assoc in PR.
     specialize (SIM1 (snoc ctx md0_tgt)). spc SIM1. rewrite Mod.add_list_snoc in SIM1. eapply SIM1 in PR.
     (***
ctx (a0 b1)
(a0 b1) ctx
a0 (b1 ctx)
(b1 ctx) a0
      ***)
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     (***
(b1 ctx) a1
a1 (b1 ctx)
(a1 b1) ctx
ctx (a1 b1)
      ***)
     specialize (SIM0 (cons md1_src ctx)). spc SIM0. rewrite Mod.add_list_cons in SIM0. eapply SIM0 in PR.
     eapply ModL.add_comm in PR.
     rewrite ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     ss.
   Qed.

(*    Theorem refines_proper_r *)
(*          (md0_src md0_tgt: Mod.t) (ctx: list Mod.t) *)
(*          (SIM0: refines md0_tgt md0_src) *)
(*      : *)
(*        <<SIM: refines (ModL.add md0_tgt (add_list ctx)) (ModL.add md0_src (add_list ctx))>> *)
(*    . *)
(*    Proof. *)
(*      ii. r in SIM0. rename ctx into xs. rename ctx0 into ys. *)
(*      (*** *)
(* ys + (tgt + xs) *)
(* (tgt + xs) + ys *)
(* tgt + (xs + ys) *)
(* (xs + ys) + tgt *)
(*       ***) *)
(*      eapply ModL.add_comm in PR. *)
(*      rewrite <- ModL.add_assoc' in PR. *)
(*      eapply ModL.add_comm in PR. *)
(*      (*** *)
(* (xs + ys) + src *)
(* src + (xs + ys) *)
(* (src + xs) + ys *)
(* ys + (src + xs) *)
(*       ***) *)
(*      specialize (SIM0 (xs ++ ys)). spc SIM0. rewrite add_list_app in SIM0. eapply SIM0 in PR. *)
(*      eapply ModL.add_comm in PR. *)
(*      rewrite ModL.add_assoc' in PR. *)
(*      eapply ModL.add_comm in PR. *)
(*      ss. *)
(*    Qed. *)
   Theorem refines_proper_r
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines (ModL.add (Mod.add_list mds0_tgt) (Mod.add_list ctx)) (ModL.add (Mod.add_list mds0_src) (Mod.add_list ctx))>>
   .
   Proof.
     ii. r in SIM0. rename ctx into xs. rename ctx0 into ys.
     (***
ys + (tgt + xs)
(tgt + xs) + ys
tgt + (xs + ys)
(xs + ys) + tgt
      ***)
     eapply ModL.add_comm in PR.
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     (***
(xs + ys) + src
src + (xs + ys)
(src + xs) + ys
ys + (src + xs)
      ***)
     specialize (SIM0 (xs ++ ys)). spc SIM0. rewrite Mod.add_list_app in SIM0. eapply SIM0 in PR.
     eapply ModL.add_comm in PR.
     rewrite ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     ss.
   Qed.

   Theorem refines_proper_l
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_tgt)) (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_src))>>
   .
   Proof.
     ii. r in SIM0. rename ctx into xs. rename ctx0 into ys.
     (***
ys + (xs + tgt)
(ys + xs) + tgt
(ys + xs) + src
ys + (xs + src)
      ***)
     rewrite ModL.add_assoc' in PR.
     specialize (SIM0 (ys ++ xs)). spc SIM0. rewrite Mod.add_list_app in SIM0. eapply SIM0 in PR.
     rewrite <- ModL.add_assoc' in PR.
     ss.
   Qed.

   Theorem refines_comm
           (x y: ModL.t)
     :
       <<SIM: refines (ModL.add x y) (ModL.add y x)>>
   .
   Proof.
     ii.
   Abort.

   Theorem adequacy_local md_src md_tgt
           (SIM: ModPair.sim md_src md_tgt)
     (*** You will need some wf conditions for ctx ***)
     :
       <<CR: (refines md_tgt md_src)>>
   .
   Proof.
     ii. eapply ModLPair.adequacy_local_closed; eauto. econs.
     { ss. red. ii. eapply ModSemLPair.add_modsempair.
       { admit "ModSemL wf". }
       { admit "ModSemL wf". }
       { clear - ctx. induction ctx.
         - ss. econs; et.
           + instantiate (1:=top2). typeclasses eauto.
           + econs.
           + ss.
         - ss. eapply ModSemLPair.add_modsempair; et.
           + admit "ModSemL wf".
           + admit "ModSemL wf".
           + eapply adequacy_lift. eapply ModSemPair.self_sim_mod. r. admit "ModSemL wf". }
       { eapply SIM. 
         admit "ModLPair.adequacy_local_closed". 
         admit "ModLPair.adequacy_local_closed". }
     }
     { ss. red. f_equal. eapply SIM. }
     { ii. red. ss. admit "ModSemL wf". }
   Qed.

   Corollary adequacy_local_list
             mds_src mds_tgt
             (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt)
     :
       <<CR: refines (Mod.add_list mds_tgt) (Mod.add_list mds_src)>>
   .
   Proof.
     r. induction FORALL; ss.
     rewrite ! Mod.add_list_cons.
     etrans.
     { rewrite <- Mod.add_list_single. eapply refines_proper_r. rewrite ! Mod.add_list_single. eapply adequacy_local; et. }
     replace (Mod.lift x) with (Mod.add_list [x]); cycle 1.
     { cbn. rewrite ModL.add_empty_r. refl. }
     eapply refines_proper_l; et.
   Qed.

End SIMMOD.
