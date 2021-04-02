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
      fn varg k_src k_tgt
      (K: forall vret,
          exists i1, sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src vret) ((mrs_tgt0, fr_tgt0), k_tgt vret))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Syscall fn varg) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Syscall fn varg) >>= k_tgt)
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
      gstep. econs; eauto.
      { rr. esplits; ss. }
      ii. ss. des; ss.  subst. unfold alist_add. ss.
      exploit K; et. i; des. pclearbot. exists i1.
      ired. gstep. econs; et. gbase. eapply CIH; et.
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
       forall skenv, <<SIM: ModSemLPair.sim (md_src.(Mod.get_modsem) skenv) (md_tgt.(Mod.get_modsem) skenv)>>;
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
  Qed.

End ADQ.

Section SIMMOD.
   Context `{Σ: GRA.t}.

   Theorem adequacy_local md_src md_tgt
           (SIM: ModPair.sim md_src md_tgt)
     (*** You will need some wf conditions for ctx ***)
     :
       <<CR: forall (ctx: Mod.t), Beh.of_program (ModL.compile (ModL.add ctx md_tgt)) <1=
                                  Beh.of_program (ModL.compile (ModL.add ctx md_src))>>
   .
   Proof.
     ii. eapply ModLPair.adequacy_local_closed; eauto. econs.
     { ss. red. ii. eapply ModSemLPair.add_modsempair.
       { admit "ModSemL wf". }
       { admit "ModSemL wf". }
       { eapply adequacy_lift. eapply ModSemPair.self_sim_mod. r. admit "ModSemL wf". }
       { eapply SIM. }
     }
     { ss. red. f_equal. eapply SIM. }
     { ii. red. ss. admit "ModSemL wf". }
   Qed.

   Theorem adequacy_local_strong md_src md_tgt
           (SIM: ModPair.sim md_src md_tgt)
     (*** You will need some wf conditions for ctx ***)
     :
       <<CR: forall ctx (WF: exists ctxs, ctx = ModL.add_list (List.map Mod.lift ctxs)),
         Beh.of_program (ModL.compile (ModL.add ctx md_tgt)) <1=
         Beh.of_program (ModL.compile (ModL.add ctx md_src))>>
   .
   Proof.
     ii. eapply ModLPair.adequacy_local_closed; eauto. econs.
     { ss. red. ii. eapply ModSemLPair.add_modsempair.
       { admit "ModSemL wf". }
       { admit "ModSemL wf". }
       { des. subst. clear - ctxs. induction ctxs.
         - ss. econs; et.
           + instantiate (1:=top2). typeclasses eauto.
           + econs.
           + ss.
         - ss. eapply ModSemLPair.add_modsempair; et.
           + admit "ModSemL wf".
           + admit "ModSemL wf".
           + eapply adequacy_lift. eapply ModSemPair.self_sim_mod. r. admit "ModSemL wf". }
       { eapply SIM. }
     }
     { ss. red. f_equal. eapply SIM. }
     { ii. red. ss. admit "ModSemL wf". }
   Qed.
End SIMMOD.

Section SIMMODS.
  Context `{Σ: GRA.t}.

  (* Lemma sim_list_adequacy (mds_src mds_tgt: list Mod.t) *)
  (*       (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt) *)
  (*   : *)
  (*     <<CR: forall (ctx: Mod.t), Beh.of_program (ModL.compile (ModL.add ctx (ModL.add_list (List.map Mod.lift mds_tgt)))) <1= *)
  (*                                Beh.of_program (ModL.compile (ModL.add ctx (ModL.add_list (List.map Mod.lift mds_src))))>>. *)
  (* Proof. *)
  (*   induction FORALL; ss. *)
  (*   cut (forall ctx, *)
  (*           Beh.of_program (ModL.compile (ModL.add ctx (ModL.add y (ModL.add_list (List.map Mod.lift l'))))) <1= *)
  (*           Beh.of_program (ModL.compile (ModL.add ctx (ModL.add y (ModL.add_list (List.map Mod.lift l)))))). *)
  (*   { ii. eapply H0 in PR. *)
  (*     apply ModL.add_comm in PR. apply ModL.add_comm. *)
  (*     erewrite <- ModL.add_assoc in *. *)
  (*     apply ModL.add_comm in PR. apply ModL.add_comm. *)
  (*     eapply adequacy_local_strong. *)
  (*     { eauto. } *)
  (*     { exists (snoc l ctx). ss. *)
  (*       clear - l. ginduction l; ii; ss. *)
  (*       { rewrite ModL.add_empty_l, ModL.add_empty_r. ss. } *)
  (*       { rewrite ModL.add_assoc. rewrite ModL.add_empty_l, ModL.add_empty_r. ss. } *)
  (*       esplits. ss. admit "". } *)
  (*     { eapply PR. } *)
  (*   } *)
  (*   { i. erewrite ModL.add_assoc in *. eapply IHFORALL. auto. } *)
  (* Qed. *)
  Lemma sim_list_adequacy_strong (mds_src mds_tgt: list Mod.t)
        (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt)
    :
      <<CR: forall ctx (WF: exists ctxs, ctx = ModL.add_list (List.map Mod.lift ctxs)),
        Beh.of_program (ModL.compile (ModL.add ctx (ModL.add_list (List.map Mod.lift mds_tgt)))) <1=
        Beh.of_program (ModL.compile (ModL.add ctx (ModL.add_list (List.map Mod.lift mds_src))))>>.
  Proof.
    induction FORALL; ss.
    cut (forall ctx (WF: exists ctxs, ctx = ModL.add_list (List.map Mod.lift ctxs)),
            Beh.of_program (ModL.compile (ModL.add ctx (ModL.add y (ModL.add_list (List.map Mod.lift l'))))) <1=
            Beh.of_program (ModL.compile (ModL.add ctx (ModL.add y (ModL.add_list (List.map Mod.lift l)))))).
    { ii. eapply H0 in PR; cycle 1.
      { des. esplits; eauto. }
      apply ModL.add_comm in PR. apply ModL.add_comm.
      erewrite <- ModL.add_assoc in *.
      apply ModL.add_comm in PR. apply ModL.add_comm.
      eapply adequacy_local_strong.
      { eauto. }
      { des. subst. exists (l ++ ctxs). ss.
        clear - l.
        replace (ModL.add_list (List.map Mod.lift l)) with (List.fold_right ModL.add ModL.empty (List.map Mod.lift l)); cycle 1.
        { refl. }
        replace (ModL.add_list (List.map Mod.lift (l ++ ctxs))) with (List.fold_right ModL.add ModL.empty (List.map Mod.lift (l ++ ctxs))); cycle 1.
        { refl. }
        rewrite map_app. rewrite fold_right_app.
        ginduction l; ii; ss.
        { ginduction ctxs; ii; ss. }
        { erewrite <- IHl. rewrite ModL.add_assoc'. ss. }
      }
      { eapply PR. }
    }
    { i. erewrite ModL.add_assoc in *. eapply IHFORALL; auto. des. subst.
      replace (ModL.add_list (List.map Mod.lift ctxs)) with (List.fold_right ModL.add ModL.empty (List.map Mod.lift ctxs)); cycle 1.
      { refl. }
      (* eexists (y :: ctxs ). *)
      (* replace (ModL.add_list (List.map Mod.lift (y :: ctxs))) with (List.fold_right ModL.add ModL.empty (List.map Mod.lift (y :: ctxs))); cycle 1. *)
      (* { refl. } *)
      (* ss. *)
      eexists (ctxs ++ [y]).
      replace (ModL.add_list (List.map Mod.lift (ctxs ++ [y]))) with (List.fold_right ModL.add ModL.empty (List.map Mod.lift (ctxs ++ [y]))); cycle 1.
      { refl. }
      rewrite map_app. rewrite fold_right_app. ss. rewrite ModL.add_empty_r.
      clear - ctxs. ginduction ctxs; ii; ss. rewrite <- IHctxs. rewrite ModL.add_assoc'. ss.
    }
  Qed.

  Lemma sim_list_adequacy_closed (mds_src mds_tgt: list ModL.t)
        (FORALL: List.Forall2 sim mds_src mds_tgt)
    :
      Beh.of_program (ModL.compile (ModL.add_list mds_tgt)) <1=
      Beh.of_program (ModL.compile (ModL.add_list mds_src)).
  Proof.
    hexploit sim_list_adequacy.
    { eauto. }
    i. specialize (H ModL.empty). repeat rewrite ModL.add_empty_l in H. auto.
  Qed.
End SIMMODS.







   Hint Resolve cpn5_wcompat: paco.

   Definition eqv (mrsl: alist string (Σ * Any.t)) (mrs: string -> Σ) (mps: string -> Any.t): Prop :=
     forall mn mn' mr mp
            (FIND: find (fun mnr : string * (Σ * Any.t) => dec mn (fst mnr)) mrsl = Some (mn', (mr, mp))),
       mrs mn = mr /\ mps mn = mp.

   Lemma lookup_find (mrsl: alist string (Σ * Any.t)) mn mr
         (LOOKUP: Maps.lookup mn mrsl = Some mr)
     :
       find (fun mnr : string * (Σ * Any.t) => dec mn (fst mnr)) mrsl = Some (mn, mr).
   Proof.
     induction mrsl; ss. unfold sumbool_to_bool. des_ifs; ss; eauto.
     { eapply neg_rel_dec_correct in Heq0. ss. }
     { rewrite rel_dec_correct in Heq0. ss. }
   Qed.

   Lemma find_lookup (mrsl: alist string (Σ * Any.t)) mn0 mn1 mr
         (FIND: find (fun mnr : string * (Σ * Any.t) => dec mn0 (fst mnr)) mrsl = Some (mn1, mr))
     :
       mn0 = mn1 /\ Maps.lookup mn0 mrsl = Some mr.
   Proof.
     induction mrsl; ss.
     unfold sumbool_to_bool in *. des_ifs; auto.
     { rewrite rel_dec_correct in Heq. ss. }
     { eapply neg_rel_dec_correct in Heq. ss. }
   Qed.

   Lemma eqv_lookup_mr mrsl mrs mps (EQV: eqv mrsl mrs mps)
         mn mr mp
         (LOOKUP: Maps.lookup mn mrsl = Some (mr, mp))
     :
       mrs mn = mr.
   Proof.
     eapply lookup_find in LOOKUP.
     eapply EQV in LOOKUP. des; auto.
   Qed.

   Lemma eqv_lookup_mp mrsl mrs mps (EQV: eqv mrsl mrs mps)
         mn mr mp
         (LOOKUP: Maps.lookup mn mrsl = Some (mr, mp))
     :
       mps mn = mp.
   Proof.
     eapply lookup_find in LOOKUP.
     eapply EQV in LOOKUP. des; auto.
   Qed.

   Lemma eqv_add_mr mrsl mrs mps (EQV: eqv mrsl mrs mps)
         mn mr0 mr1 mp0
         (LOOKUP: Maps.lookup mn mrsl = Some (mr0, mp0))
     :
       eqv (Maps.add mn (mr1, mp0) mrsl) (update mrs mn mr1) mps.
   Proof.
     ii. eapply find_lookup in FIND. des; subst.
     simpl. unfold update. des_ifs.
     { assert (lookup mn' (add mn' (mr1, mp0) mrsl) = Some (mr1, mp0)).
       { eapply mapsto_lookup. eapply mapsto_add_eq. }
       clarify. split; auto. eapply eqv_lookup_mp in LOOKUP; eauto.
     }
     { split.
       { eapply eqv_lookup_mr; eauto. eapply mapsto_lookup in FIND0.
         eapply mapsto_lookup. eapply mapsto_add_neq; eauto. }
       { eapply eqv_lookup_mp; eauto. eapply mapsto_lookup in FIND0.
         eapply mapsto_lookup. eapply mapsto_add_neq; eauto. }
     }
   Qed.

   Lemma eqv_add_ms mrsl mrs mps (EQV: eqv mrsl mrs mps)
         mn mr0 mp0 mp1
         (LOOKUP: Maps.lookup mn mrsl = Some (mr0, mp0))
     :
       eqv (Maps.add mn (mr0, mp1) mrsl) mrs (update mps mn mp1).
   Proof.
     ii. eapply find_lookup in FIND. des; subst.
     simpl. unfold update. des_ifs.
     { assert (lookup mn' (add mn' (mr0, mp1) mrsl) = Some (mr0, mp1)).
       { eapply mapsto_lookup. eapply mapsto_add_eq. }
       clarify. split; auto. eapply eqv_lookup_mr in LOOKUP; eauto.
     }
     { split.
       { eapply eqv_lookup_mr; eauto. eapply mapsto_lookup in FIND0.
         eapply mapsto_lookup. eapply mapsto_add_neq; eauto. }
       { eapply eqv_lookup_mp; eauto. eapply mapsto_lookup in FIND0.
         eapply mapsto_lookup. eapply mapsto_add_neq; eauto. }
     }
   Qed.

   Variant lift_wf (wf: alist string (Σ * Any.t) * alist string (Σ * Any.t) -> Prop)
           (mrs_src mrs_tgt: string -> Σ) (mps_src mps_tgt: string -> Any.t): Prop :=
   | lift_wf_intro
       mrsl_src mrsl_tgt
       (EQVSRC: eqv mrsl_src mrs_src mps_src)
       (EQVTGT: eqv mrsl_tgt mrs_tgt mps_tgt)
       (WF: wf (mrsl_src, mrsl_tgt))
   .

   Let arith (o: Ord.t) (n0: nat) (n1: nat): Ord.t :=
     (n0 * o + n1)%ord.

   Let arith_lt_1 o0 o1 n0 n1 n2
         (OLT: (o0 < o1)%ord)
         (LT: n1 < n0 + n2)
     :
       Ord.lt (arith o0 n0 n1) (arith o1 n0 n2).
   Proof.
     unfold arith. eapply Ord.lt_le_lt.
     2: {
       eapply OrdArith.le_add_l.
       eapply OrdArith.le_mult_r.
       eapply Ord.S_supremum. eauto.
     }
     eapply Ord.lt_eq_lt.
     { eapply OrdArith.eq_add_l.
       eapply OrdArith.mult_S.
     }
     eapply Ord.lt_eq_lt.
     { eapply OrdArith.add_assoc. }
     eapply OrdArith.lt_add_r.
     eapply Ord.lt_eq_lt.
     { symmetry. eapply OrdArith.add_from_nat.  }
     eapply OrdArith.lt_from_nat. eauto.
   Qed.

   Lemma arith_lt_2 o n0 n1 n2
         (LT: (n1 < n2)%nat)
     :
       Ord.lt (arith o n0 n1) (arith o n0 n2).
   Proof.
     eapply OrdArith.lt_add_r. eapply OrdArith.lt_from_nat. eauto.
   Qed.

   Lemma lift_sim ms_src ms_tgt
         (wf: alist string (Σ * Any.t) * alist string (Σ * Any.t) -> Prop)
         (FNS: forall fn : string,
             option_rel (sim_fnsem wf)
                        (find (fun fnsem : string * (Any.t -> itree Es Any.t) => dec fn (fst fnsem))
                              (ModSemL.fnsems ms_src))
                        (find (fun fnsem : string * (Any.t -> itree Es Any.t) => dec fn (fst fnsem))
                              (ModSemL.fnsems ms_tgt)))
     :
       forall n mrsl_src fr_src f_src mrsl_tgt fr_tgt f_tgt
              (* (WF: wf (mrsl_src, mrsl_tgt)) *)
              (SIM: sim_itree wf n (mrsl_src, fr_src, f_src) (mrsl_tgt, fr_tgt, f_tgt))
              mrs_src mrs_tgt mps_src mps_tgt
              (EQVSRC: eqv mrsl_src mrs_src mps_src)
              (EQVTGT: eqv mrsl_tgt mrs_tgt mps_tgt)
              frs_src frs_tgt,
         simg (fun (vret_src vret_tgt: r_state * p_state * Any.t) =>
                 exists fr_src' fr_tgt',
                   (<<WF: lift_wf wf (fst (fst (fst vret_src))) (fst (fst (fst vret_tgt))) (snd (fst vret_src)) (snd (fst vret_tgt))>>) /\
                   (<<FRSRC: snd (fst (fst vret_src)) = fr_src'::frs_src>>) /\
                   (<<FRTGT: snd (fst (fst vret_tgt)) = fr_tgt'::frs_tgt>>) /\
                   (<<VAL: snd vret_src = snd vret_tgt>>)) (arith n 4 4)
              (interp_Es
                 (ModSemL.prog ms_src)
                 f_src
                 (mrs_src, fr_src::frs_src, mps_src))
              (interp_Es
                 (ModSemL.prog ms_tgt)
                 f_tgt
                 (mrs_tgt, fr_tgt::frs_tgt, mps_tgt)).
   Proof.
     ginit. gcofix CIH. i.
     punfold SIM. gstep. Local Opaque interp_Es.
     inv SIM; pclearbot; ss; mgo; ss; mgo.
     - econs; ss. esplits; et. econs; eauto.
     - econs; ss. gbase. eapply CIH; eauto.
     - econs; ss. unfold unwrapU.
       generalize (FNS fn). i. inv H; cycle 1.
       { clear H1 H2. unfold triggerUB. mgo.
         gstep. econs; ss.
       }
       clear H1 H2. mgo.
       destruct a as [fn_src f_src]. destruct b as [fn_tgt f_tgt].
       inv IN. inv H. simpl in H1. clarify.
       exploit H0; eauto. instantiate (2:=varg). i. des.
       mgo. ss.
       erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)).
       erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       gstep. econs; auto.
       gstep. econs; auto.
       gclo. eapply wrespect5_companion; auto with paco.
       { eapply bindC_wrespectful. }
       econs.
       + gbase. eapply CIH; eauto.
       + i. ss. des.
         destruct vret_src as [[mrs_src' frs_src'] val_src].
         destruct vret_tgt as [[mrs_tgt' frs_tgt'] val_tgt].
         destruct mrs_src', mrs_tgt'. ss. subst. mgo. ss. mgo.
         gstep. econs; auto.
         inv WF0. hexploit K; eauto. i. des. pclearbot.
         eapply CIH in H; eauto; ss.
         gstep. econs; auto.
         gbase. eapply H.
     - econs. ii. mgo.
       gstep. econs; auto.
       gstep. econs; auto.
       subst. hexploit K; eauto. i. des. pclearbot.
       eapply CIH in H; eauto; ss.
       gstep. econs; auto.
       gbase. eapply H.
     - econs; eauto. i. hexploit K; eauto. i. des. pclearbot.
       eexists. mgo.
       gstep. econs; auto.
       gstep. econs; auto.
       gstep. econs; auto.
       gbase. eapply CIH; eauto.
     - econs; eauto. i. hexploit K; eauto. i. des. pclearbot.
       eexists. mgo.
       gstep. econs; auto.
       gstep. econs; auto.
       gstep. econs; auto.
       gbase. eapply CIH; eauto.
     - erewrite interp_Es_pE with (rst0:=(mrs_src, fr_src :: frs_src)).
       erewrite interp_Es_pE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       gstep. econs; auto.
       gstep. econs; auto.
       gbase. eapply CIH; eauto.
       { eapply eqv_add_ms; eauto. }
       { eapply eqv_add_ms; eauto. }
     - erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)).
       erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       gstep. econs; auto.
       gbase. eapply CIH; eauto.
       { eapply eqv_add_mr; eauto. }
       { eapply eqv_add_mr; eauto. }
     - erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)).
       erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       ecith (rst0:=(mrs_src, fr_src :: frs_src)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
       { eapply eqv_add_ms; eauto. }
     - erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)).  ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
       { eapply eqv_add_mr; eauto. }
     - erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - eapply eqv_lookup_mp in MR0; eauto. subst.
       erewrite interp_Es_pE with (rst0:=(mrs_src, fr_src :: frs_src)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - eapply eqv_lookup_mr in MR0; eauto. subst.
       erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - econs; eauto.
       { eapply arith_lt_1 with (n1:=4); auto.
         - eassumption.
         - clear. lia. }
       gbase. eapply CIH; eauto.
     - econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       i. mgo. gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=5); auto. }
       gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto. eapply K.
     - des. pclearbot. econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       eexists. mgo. gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=5); auto. }
       gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - erewrite interp_Es_pE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
       { eapply eqv_add_ms; eauto. }
     - erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
       { eapply eqv_add_mr; eauto. }
     - erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - eapply eqv_lookup_mp in MR0; eauto. subst.
       erewrite interp_Es_pE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - eapply eqv_lookup_mr in MR0; eauto. subst.
       erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
       Unshelve. all: exact O.
   Qed.


   Theorem adequacy_local_closed
           (SIM: sim)
     :
       Beh.of_program (Mod.compile md_tgt) <1=
       Beh.of_program (Mod.compile md_src)
   .
   Proof.
     inv SIM. specialize (sim_modsem0 (Sk.load_skenv (Mod.sk md_src))).
     inv sim_modsem0. red in sim_sk0.

     eapply adequacy_global; et. exists (OrdArith.add Ord.O Ord.O).
     unfold ModSemL.initial_itr, Mod.enclose.

     assert (FNS: forall fn : string,
                option_rel (sim_fnsem wf)
                           (find (fun fnsem : string * (Any.t -> itree Es Any.t) => dec fn (fst fnsem))
                                 (ModSemL.fnsems (Mod.get_modsem md_src (Sk.load_skenv (Mod.sk md_src)))))
                           (find (fun fnsem : string * (Any.t -> itree Es Any.t) => dec fn (fst fnsem))
                                 (ModSemL.fnsems (Mod.get_modsem md_tgt (Sk.load_skenv (Mod.sk md_tgt)))))).
     { rewrite <- sim_sk0 in *.
       remember (ModSemL.fnsems (Mod.get_modsem md_src (Sk.load_skenv (Mod.sk md_src)))).
       remember (ModSemL.fnsems (Mod.get_modsem md_tgt (Sk.load_skenv (Mod.sk md_src)))).
       clear - sim_fnsems. induction sim_fnsems; ss.
       i. unfold sumbool_to_bool. des_ifs; eauto.
       - inv H. ss.
       - inv H. exfalso. eapply n. ss.
     }

     ginit. unfold assume. mgo.
     gstep. econs; eauto. i. esplits; eauto.
     { eapply sim_wf0. rewrite sim_sk0 in *. ss. } clear x_src.
     ss. unfold ITree.map, unwrapU, triggerUB. mgo.
     generalize (FNS "main"). i. inv H.
     2: { mgo. gstep. econs; eauto. ss. }
     destruct a, b. inv IN. mgo.
     exploit H0; eauto. i. des.
     ss. mgo.
     gstep. econs; eauto. gstep. econs; eauto.
     guclo bindC_spec. econs.
     { gfinal. right. eapply lift_sim.
       { eapply FNS. }
       { eapply x. }
       { ii. unfold ModSemL.initial_p_state. des_ifs. }
       { ii. rewrite sim_sk0 in *. unfold ModSemL.initial_p_state. des_ifs. }
     }
     { i. ss. des.
       destruct vret_src as [[[mrs_src frs_src] p_src] v_src].
       destruct vret_tgt as [[[mrs_tgt frs_tgt] p_tgt] v_tgt]. ss. subst.
       mgo. ss. mgo.
       gstep. econs; eauto.
       gstep. econs; eauto.
       gstep. econs; eauto.
     }
     Unshelve. all: exact Ord.O.
   Qed.

   (* Theorem adequacy_local *)
   (*         (SIM: sim) *)
   (*         (*** You will need some wf conditions for ctx ***) *)
   (*   : *)
   (*     <<CR: forall ctx, Beh.of_program (Mod.compile (Mod.add ctx md_tgt)) <1= *)
   (*                       Beh.of_program (Mod.compile (Mod.add ctx md_src))>> *)
   (* . *)
   (* Proof. *)
   (*   ii. eapply adequacy_global; et. exists Ordinal.O. *)
   (*   admit "TODO". *)
   (* Qed. *)

End SIMMOD.

Section SIMMOD.
   Context `{Σ: GRA.t}.

   Theorem adequacy_local md_src md_tgt
           (SIM: sim md_src md_tgt)
     (*** You will need some wf conditions for ctx ***)
     :
       <<CR: forall ctx, Beh.of_program (Mod.compile (Mod.add ctx md_tgt)) <1=
                         Beh.of_program (Mod.compile (Mod.add ctx md_src))>>
   .
   Proof.
     ii. eapply adequacy_local_closed; eauto. econs.
     { ss. red. ii. eapply ModSemLPair.add_modsempair.
       { admit "ModSemL wf". }
       { admit "ModSemL wf". }
       { eapply ModSemLPair.self_sim_mod. admit "ModSemL wf". }
       { eapply SIM. }
     }
     { ss. red. f_equal. eapply SIM. }
     { ii. red. ss. admit "ModSemL wf". }
   Qed.
End SIMMOD.

Section SIMMODS.
  Context `{Σ: GRA.t}.

  Lemma sim_list_adequacy (mds_src mds_tgt: list Mod.t)
        (FORALL: List.Forall2 sim mds_src mds_tgt)
    :
      <<CR: forall ctx, Beh.of_program (Mod.compile (Mod.add ctx (Mod.add_list mds_tgt))) <1=
                        Beh.of_program (Mod.compile (Mod.add ctx (Mod.add_list mds_src)))>>.
  Proof.
    induction FORALL; ss.
    cut (forall ctx,
            Beh.of_program (Mod.compile (Mod.add ctx (Mod.add y (Mod.add_list l')))) <1=
            Beh.of_program (Mod.compile (Mod.add ctx (Mod.add y (Mod.add_list l))))).
    { ii. eapply H0 in PR.
      apply Mod.add_comm in PR. apply Mod.add_comm.
      erewrite <- Mod.add_assoc in *.
      apply Mod.add_comm in PR. apply Mod.add_comm.
      eapply adequacy_local.
      { eauto. }
      { eapply PR. }
    }
    { i. erewrite Mod.add_assoc in *. eapply IHFORALL. auto. }
  Qed.

  Lemma sim_list_adequacy_closed (mds_src mds_tgt: list Mod.t)
        (FORALL: List.Forall2 sim mds_src mds_tgt)
    :
      Beh.of_program (Mod.compile (Mod.add_list mds_tgt)) <1=
      Beh.of_program (Mod.compile (Mod.add_list mds_src)).
  Proof.
    hexploit sim_list_adequacy.
    { eauto. }
    i. specialize (H Mod.empty). repeat rewrite Mod.add_empty_l in H. auto.
  Qed.
End SIMMODS.
End ModPair.

(* TODO: prove sim *)
(* TODO: write client *)
(* TODO: show cancellation *)
(* TODO: meta-level (no forge -> checkwf always succeeds) *)
