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

Set Implicit Arguments.

Local Open Scope nat_scope.










Section SIM.
  Let st_local: Type := (Any.t).

  Variable world: Type.

  Let W: Type := (Any.t) * (Any.t).
  Variable wf: world -> W -> Prop.
  Variable le: relation world.


  Inductive _sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
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
          sim_itree _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itree_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: exists (x: X), _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itree_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_pput_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      st_src1
      (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_pget_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
                 (st_tgt0, i_tgt)


  | sim_itree_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itree_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: exists (x: X), _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Take X) >>= k_tgt)

  | sim_itree_pput_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      st_tgt1
      (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | sim_itree_pget_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PGet) >>= k_tgt)

  | sim_itree_progress
      i_src0 i_tgt0 w0 st_src0 st_tgt0 i_src i_tgt
      (SIM: sim_itree _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
      (SRC: i_src0 = true)
      (TGT: i_tgt0 = true)
    :
      _sim_itree sim_itree RR true true w0 (st_src0, i_src) (st_tgt0, i_tgt)
  .

  Definition lift_rel {R_src R_tgt} (w0: world) (RR: R_src -> R_tgt -> Prop)
             (st_src st_tgt: st_local) (ret_src ret_tgt : Any.t) :=
    exists w1 : world,
      (<<WLE: le w0 w1 >> /\ <<WF: wf w1 (st_src, st_tgt) >> /\ <<RET: ret_src = ret_tgt >>).

  Lemma _sim_itree_ind2 (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        (P: bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        (RET: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            v_src v_tgt
            (RET: RR st_src0 st_tgt0 v_src v_tgt),
            P i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt)))
        (CALL: forall
            i_src0 i_tgt0 w w0 st_src0 st_tgt0
            fn varg k_src k_tgt
            (WF: wf w0 (st_src0, st_tgt0))
            (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
                sim_itree _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret)),
            P i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
              (st_tgt0, trigger (Call fn varg) >>= k_tgt))
        (SYSCALL: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            fn varg rvs k_src k_tgt
            (K: forall vret,
                sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
              (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt))
        (TAUSRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt))
        (CHOOSESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: exists (x: X), <<SIM: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
              (st_tgt0, i_tgt))
        (TAKESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: forall (x: X), <<SIM: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
              (st_tgt0, i_tgt))
        (PPUTSRC: forall
            i_src0 i_tgt0 w0 st_tgt0 st_src0
            k_src i_tgt
            st_src1
            (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
              (st_tgt0, i_tgt))
        (PGETSRC: forall
            i_src0 i_tgt0 w0 st_tgt0 st_src0
            k_src i_tgt
            (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
              (st_tgt0, i_tgt))
        (TAUTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt))
        (CHOOSETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Choose X) >>= k_tgt))
        (TAKETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: exists (x: X), <<SIM:_sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Take X) >>= k_tgt))
        (PPUTTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt i_src
            st_tgt1
            (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt))
        (PGETTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt i_src
            (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0)),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (PGet) >>= k_tgt))
        (PROGRESS: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0 i_src i_tgt
            (SIM: sim_itree _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (SRC: i_src0 = true)
            (TGT: i_tgt0 = true),
            P true true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      forall i_src0 i_tgt0 w0 st_src st_tgt
             (SIM: _sim_itree sim_itree RR i_src0 i_tgt0 w0 st_src st_tgt),
        P i_src0 i_tgt0 w0 st_src st_tgt.
  Proof.
    fix IH 6. i. inv SIM.
    { eapply RET; eauto. }
    { eapply CALL; eauto. }
    { eapply SYSCALL; eauto. }
    { eapply TAUSRC; eauto. }
    { eapply CHOOSESRC; eauto. des. esplits; eauto. }
    { eapply TAKESRC; eauto. }
    { eapply PPUTSRC; eauto. }
    { eapply PGETSRC; eauto. }
    { eapply TAUTGT; eauto. }
    { eapply CHOOSETGT; eauto. }
    { eapply TAKETGT; eauto. des. esplits; eauto. }
    { eapply PPUTTGT; eauto. }
    { eapply PGETTGT; eauto. }
    { eapply PROGRESS; eauto. }
  Qed.

  Definition sim_itree o_src o_tgt w0: relation _ :=
    paco8 _sim_itree bot8 _ _ (lift_rel w0 (@eq Any.t)) o_src o_tgt w0.

  Lemma sim_itree_mon: monotone8 _sim_itree.
  Proof.
    ii. induction IN using _sim_itree_ind2; try (by des; econs; ss; et).
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree_mon: paco.
  Hint Resolve cpn8_wcompat: paco.

  Lemma sim_itree_ind
        R_src R_tgt (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        (P: bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        (RET: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            v_src v_tgt
            (RET: RR st_src0 st_tgt0 v_src v_tgt),
            P i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt)))
        (CALL: forall
            i_src0 i_tgt0 w w0 st_src0 st_tgt0
            fn varg k_src k_tgt
            (WF: wf w0 (st_src0, st_tgt0))
            (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
                paco8 _sim_itree bot8 _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret)),
            P i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
              (st_tgt0, trigger (Call fn varg) >>= k_tgt))
        (SYSCALL: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            fn varg rvs k_src k_tgt
            (K: forall vret,
                paco8 _sim_itree bot8 _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
              (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt))
        (TAUSRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt))
        (CHOOSESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: exists (x: X), <<SIM: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
              (st_tgt0, i_tgt))
        (TAKESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: forall (x: X), <<SIM: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
              (st_tgt0, i_tgt))
        (PPUTSRC: forall
            i_src0 i_tgt0 w0 st_tgt0 st_src0
            k_src i_tgt
            st_src1
            (K: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
              (st_tgt0, i_tgt))
        (PGETSRC: forall
            i_src0 i_tgt0 w0 st_tgt0 st_src0
            k_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
              (st_tgt0, i_tgt))
        (TAUTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt))
        (CHOOSETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Choose X) >>= k_tgt))
        (TAKETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: exists (x: X), <<SIM:paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Take X) >>= k_tgt))
        (PPUTTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt i_src
            st_tgt1
            (K: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt))
        (PGETTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt i_src
            (K: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0)),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (PGet) >>= k_tgt))
        (PROGRESS: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0 i_src i_tgt
            (SIM: paco8 _sim_itree bot8 _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (SRC: i_src0 = true)
            (TGT: i_tgt0 = true),
            P true true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      forall i_src0 i_tgt0 w0 st_src st_tgt
             (SIM: paco8 _sim_itree bot8 _ _ RR i_src0 i_tgt0 w0 st_src st_tgt),
        P i_src0 i_tgt0 w0 st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM using _sim_itree_ind2.
    { eapply RET; eauto. }
    { eapply CALL; eauto. i. exploit K; eauto. i. pclearbot. eauto. }
    { eapply SYSCALL; eauto. i. exploit K; eauto. i. pclearbot. eauto. }
    { eapply TAUSRC; eauto. }
    { eapply CHOOSESRC; eauto. des. esplits; eauto. }
    { eapply TAKESRC; eauto. i. exploit K; eauto. i. des.
      pclearbot. esplits; eauto. }
    { eapply PPUTSRC; eauto. }
    { eapply PGETSRC; eauto. }
    { eapply TAUTGT; eauto. }
    { eapply CHOOSETGT; eauto. i. exploit K; eauto. i. des.
      pclearbot. esplits; eauto. }
    { eapply TAKETGT; eauto. des. esplits; eauto. }
    { eapply PPUTTGT; eauto. }
    { eapply PGETTGT; eauto. }
    { eapply PROGRESS; eauto. pclearbot. auto. }
  Qed.

  Variant sim_itree_indC (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_indC_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | sim_itree_indC_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          sim_itree _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                     (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_indC_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                     (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itree_indC_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: sim_itree _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_indC_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: exists (x: X), sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                     (st_tgt0, i_tgt)
  | sim_itree_indC_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                     (st_tgt0, i_tgt)

  | sim_itree_indC_pput_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      st_src1
      (K: sim_itree _ _ RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                     (st_tgt0, i_tgt)

  | sim_itree_indC_pget_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      (K: sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
                     (st_tgt0, i_tgt)


  | sim_itree_indC_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_indC_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itree_indC_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: exists (x: X), sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (Take X) >>= k_tgt)

  | sim_itree_indC_pput_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      st_tgt1
      (K: sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | sim_itree_indC_pget_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      (K: sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (PGet) >>= k_tgt)
  .

  Lemma sim_itree_indC_mon: monotone8 sim_itree_indC.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
  Qed.
  Hint Resolve sim_itree_indC_mon: paco.

  Lemma sim_itree_indC_spec:
    sim_itree_indC <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit K; eauto. i. des.
      esplits; eauto. eapply rclo8_base. eauto. }
    { econs 3; eauto. i. eapply rclo8_base. eauto. }
    { econs 4; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 5; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 6; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 7; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 8; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 9; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 10; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 11; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 12; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 13; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
  Qed.

  Variant sim_itreeC (r g: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itreeC_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | sim_itreeC_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          g _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itreeC_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          g _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itreeC_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: r _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itreeC_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: exists (x: X), r _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itreeC_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), r _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itreeC_pput_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      st_src1
      (K: r _ _ RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itreeC_pget_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      (K: r _ _ RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
                 (st_tgt0, i_tgt)


  | sim_itreeC_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itreeC_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itreeC_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: exists (x: X), r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Take X) >>= k_tgt)

  | sim_itreeC_pput_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      st_tgt1
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | sim_itreeC_pget_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PGet) >>= k_tgt)
  .

  Lemma sim_itreeC_spec_aux:
    sim_itreeC <10= gpaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    i. inv PR.
    { gstep. econs 1; eauto. }
    { gstep. econs 2; eauto. i. gbase. eauto. }
    { gstep. econs 3; eauto. i. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 4; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 5; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 6; eauto. i. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 7; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 8; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 9; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 10; eauto. i. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 11; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 12; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 13; eauto. gbase. eauto. }
  Qed.

  Lemma sim_itreeC_spec r g
    :
      @sim_itreeC (gpaco8 (_sim_itree) (cpn8 _sim_itree) r g) (gpaco8 (_sim_itree) (cpn8 _sim_itree) g g)
      <8=
      gpaco8 (_sim_itree) (cpn8 _sim_itree) r g.
  Proof.
    i. eapply gpaco8_gpaco; [eauto with paco|].
    eapply gpaco8_mon.
    { eapply sim_itreeC_spec_aux. eauto. }
    { auto. }
    { i. eapply gupaco8_mon; eauto. }
  Qed.

  Lemma sim_itree_progress_flag R0 R1 RR r g w st_src st_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) g g R0 R1 RR false false w st_src st_tgt)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR true true w st_src st_tgt.
  Proof.
    gstep. destruct st_src, st_tgt. econs; eauto.
  Qed.

  Lemma sim_itree_flag_mon
        (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        R_src R_tgt (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        f_src0 f_tgt0 f_src1 f_tgt1 w st_src st_tgt
        (SIM: @_sim_itree sim_itree _ _ RR f_src0 f_tgt0 w st_src st_tgt)
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      @_sim_itree sim_itree _ _ RR f_src1 f_tgt1 w st_src st_tgt.
  Proof.
    revert f_src1 f_tgt1 SRC TGT.
    induction SIM using _sim_itree_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. des. esplits; eauto. }
    { econs 6; eauto. i. exploit K; eauto. i. des. eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. i. exploit K; eauto. i. des. eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { exploit SRC0; auto. exploit TGT0; auto. i. clarify. econs 14; eauto. }
  Qed.

  Definition sim_fsem: relation (option mname * Any.t -> itree Es Any.t) :=
    (eq ==> (fun it_src it_tgt => forall w mrs_src mrs_tgt (SIMMRS: wf w (mrs_src, mrs_tgt)),
                 sim_itree false false w (mrs_src, it_src)
                           (mrs_tgt, it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (option mname * Any.t -> itree Es Any.t)) := RelProd eq sim_fsem.


  Variant lflagC (r: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | lflagC_intro
      f_src0 f_src1 f_tgt0 f_tgt1 w st_src st_tgt
      (SIM: r _ _ RR f_src0 f_tgt0 w st_src st_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      lflagC r RR f_src1 f_tgt1 w st_src st_tgt
  .

  Lemma lflagC_mon
        r1 r2
        (LE: r1 <8= r2)
    :
      @lflagC r1 <8= @lflagC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lflagC_mon: paco.

  Lemma lflagC_spec: lflagC <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM.
    revert x3 x4 SRC TGT. induction SIM using _sim_itree_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit K; eauto. i. des.
      esplits; eauto. eapply rclo8_base. eauto. }
    { econs 3; eauto. i. eapply rclo8_base. eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. des. esplits; eauto. }
    { econs 6; eauto. i. exploit K; eauto. i. des. esplits; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. i. exploit K; eauto. i. des. esplits; eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { exploit SRC0; auto. exploit TGT0; auto. i. clarify. econs 14; eauto.
      eapply rclo8_base; auto. }
  Qed.

  Lemma sim_itree_flag_down R0 R1 RR r g w st_src st_tgt f_src f_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR false false w st_src st_tgt)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR f_src f_tgt w st_src st_tgt.
  Proof.
    guclo lflagC_spec. econs; eauto.
  Qed.

  Lemma sim_itree_bot_flag_up R0 R1 RR w st_src st_tgt f_src f_tgt
        (SIM: paco8 _sim_itree bot8 R0 R1 RR true true w st_src st_tgt)
    :
      paco8 _sim_itree bot8 R0 R1 RR f_src f_tgt w st_src st_tgt.
  Proof.
    ginit. remember true in SIM at 1. remember true in SIM at 1.
    clear Heqb Heqb0. revert w st_src st_tgt f_src f_tgt b b0 SIM.
    gcofix CIH. i. revert f_src f_tgt.

    (* TODO: why induction using sim_itree_ind doesn't work? *)
    pattern b, b0, w, st_src, st_tgt.
    match goal with
    | |- ?P b b0 w st_src st_tgt => set P
    end.
    revert b b0 w st_src st_tgt SIM.
    eapply (@sim_itree_ind R0 R1 RR P); subst P; ss; i; clarify.
    { guclo sim_itree_indC_spec. econs 1; eauto. }
    { gstep. econs 2; eauto. i. gbase. eapply CIH; eauto. }
    { gstep. econs 3; eauto. i. gbase. eapply CIH; eauto. }
    { guclo sim_itree_indC_spec. econs 4; eauto. }
    { guclo sim_itree_indC_spec. econs 5; eauto. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 6; eauto. i. hexploit K; eauto. i. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 7; eauto. }
    { guclo sim_itree_indC_spec. econs 8; eauto. }
    { guclo sim_itree_indC_spec. econs 9; eauto. }
    { guclo sim_itree_indC_spec. econs 10; eauto. i. hexploit K; eauto. i. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 11; eauto. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 12; eauto. }
    { guclo sim_itree_indC_spec. econs 13; eauto. }
    { eapply sim_itree_flag_down. gfinal. right.
      eapply paco8_mon; eauto. ss.
    }
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), bool -> bool -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop):
    forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), bool -> bool -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop :=
  | lbindR_intro
      f_src f_tgt w0 w1

      R_src R_tgt RR
      (st_src0 st_tgt0: st_local)
      (i_src: itree Es R_src) (i_tgt: itree Es R_tgt)
      (SIM: r _ _ RR f_src f_tgt w0 (st_src0, i_src) (st_tgt0, i_tgt))

      S_src S_tgt SS
      (k_src: ktree Es R_src S_src) (k_tgt: ktree Es R_tgt S_tgt)
      (SIMK: forall st_src1 st_tgt1 vret_src vret_tgt (SIM: RR st_src1 st_tgt1 vret_src vret_tgt), s _ _ SS false false w1 (st_src1, k_src vret_src) (st_tgt1, k_tgt vret_tgt))
    :
      lbindR r s SS f_src f_tgt w1 (st_src0, ITree.bind i_src k_src) (st_tgt0, ITree.bind i_tgt k_tgt)
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
    econs.
    { ii. eapply lbindR_mon; eauto. }
    i. rename l into llll. inv PR; csc.
    remember (st_src0, i_src). remember(st_tgt0, i_tgt).
    revert st_src0 i_src st_tgt0 i_tgt Heqp Heqp0.
    revert k_src k_tgt SIMK. eapply GF in SIM.
    induction SIM using _sim_itree_ind2; i; clarify.
    + rewrite ! bind_ret_l. exploit SIMK; eauto. i.
      eapply sim_itree_flag_mon.
      { eapply sim_itree_mon; eauto. i. eapply rclo8_base. auto. }
      { ss. }
      { ss. }
    + rewrite ! bind_bind. econs; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. i. exploit K; eauto. i. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. i. exploit K; eauto. i. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
    + econs; eauto. eapply rclo8_clo_base. econs; eauto.
  Qed.

  Lemma lbindC_spec: lbindC <9= gupaco8 (_sim_itree) (cpn8 (_sim_itree)).
  Proof.
    intros. eapply wrespect8_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

End SIM.
Hint Resolve sim_itree_mon: paco.
Hint Resolve cpn8_wcompat: paco.

Lemma self_sim_itree:
  forall st itr,
    sim_itree (fun _ '(src, tgt) => src = tgt) top2 false false tt (st, itr) (st, itr).
Proof.
  ginit. gcofix CIH. i. ides itr.
  { gstep. eapply sim_itree_ret; ss. }
  { guclo sim_itree_indC_spec. econs.
    guclo sim_itree_indC_spec. econs.
    eapply sim_itree_progress_flag. gbase. auto.
  }
  destruct e.
  { dependent destruction c. rewrite <- ! bind_trigger. gstep.
    eapply sim_itree_call; ss. ii. subst.
    eapply sim_itree_flag_down. gbase. auto.
  }
  destruct s.
  { rewrite <- ! bind_trigger. resub. dependent destruction p.
    { guclo sim_itree_indC_spec. econs.
      guclo sim_itree_indC_spec. econs.
      eapply sim_itree_progress_flag. gbase. auto.
    }
    { guclo sim_itree_indC_spec. econs.
      guclo sim_itree_indC_spec. econs.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
  { rewrite <- ! bind_trigger. resub. dependent destruction e.
    { guclo sim_itree_indC_spec. econs 10. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs 6. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs. i.
      eapply sim_itree_progress_flag. gbase. auto.
    }
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

Require Import SimGlobal.
Require Import Red IRed.

Module TAC.
  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac step := ired_both; guclo simg_safe_spec; econs; et; i.
  Ltac steps := (repeat step); ired_both.

  Ltac force := ired_both; guclo simg_indC_spec; econs; et.
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
        (exists mn' (f: _ -> itree _ _),
            (<<MN: mn <> mn'>>) /\
            (<<SRC: alist_find fn ms_src.(ModSemL.fnsems) = Some (transl_all mn' (T:=Any.t) ∘ f)>>) /\
            (<<TGT: alist_find fn ms_tgt.(ModSemL.fnsems) = Some (transl_all mn' (T:=Any.t) ∘ f)>>)) \/
        (exists (f_src f_tgt: _ -> itree _ _),
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
      forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop :=
    | my_r0_intro
        w0
        (itr_src itr_tgt: itree Es Any.t)
        st_src st_tgt o_src o_tgt
        (SIM: sim_itree wf le o_src o_tgt w0 (st_src mn, itr_src) (st_tgt mn, itr_tgt))
        (STATE: forall mn' (MN: mn <> mn'), st_src mn' = st_tgt mn')
      :
        my_r0 (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
                 g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt)
              o_src o_tgt
              (EventsL.interp_Es (ModSemL.prog ms_src) (transl_all mn itr_src) st_src)
              (EventsL.interp_Es (ModSemL.prog ms_tgt) (transl_all mn itr_tgt) st_tgt)
    .

    Variant my_r1:
      forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop :=
    | my_r1_intro
        mn' w0 st_src st_tgt
        (MN: mn <> mn')
        (SIM: g_lift_rel w0 st_src st_tgt)
        (itr: itree Es Any.t)
      :
        my_r1 (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
                 g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt)
              false false
              (EventsL.interp_Es (ModSemL.prog ms_src) (transl_all mn' itr) st_src)
              (EventsL.interp_Es (ModSemL.prog ms_tgt) (transl_all mn' itr) st_tgt)
    .

    Let my_r := my_r0 \7/ my_r1.
    Let sim_lift: my_r <7= simg.
    Proof.
      ginit.
      { i. eapply cpn7_wcompat; eauto with paco. }
      gcofix CIH. i. destruct PR.
      { destruct H.
        unfold sim_itree in SIM.
        remember (st_src mn, itr_src).
        remember (st_tgt mn, itr_tgt).
        remember w0 in SIM at 2.
        revert st_src itr_src st_tgt itr_tgt Heqp Heqp0 Heqw STATE.

        (* TODO: why induction using sim_itree_ind doesn't work? *)
        pattern o_src, o_tgt, w, p, p0.
        match goal with
        | |- ?P o_src o_tgt w p p0 => set P
        end.
        revert o_src o_tgt w p p0 SIM.
        eapply (@sim_itree_ind world wf le Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; clarify.

        - rr in RET. des. step. splits; auto. econs; et.
        - hexploit (fnsems_find_iff fn). i. des.
          { steps. rewrite NONE. unfold unwrapU, triggerUB. step. ss. }
          { steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
            apply simg_progress_flag.
            guclo bindC_spec. econs.
            { gbase. eapply CIH. right. econs; ss. econs; et. refl. }
            { i. ss. des. destruct vret_src, vret_tgt. des; clarify. inv SIM.
              hexploit K; et. i. des. pclearbot.
              steps. gbase. eapply CIH. left. econs; et.
            }
          }
          { hexploit (SIM (Some mn, varg) (Some mn, varg)); et. i. des.
            steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
            apply simg_progress_flag.
            guclo bindC_spec. econs.
            { gbase. eapply CIH. left. econs; ss. et. }
            { i. ss. destruct vret_src, vret_tgt. des; clarify. inv SIM0.
              hexploit K; et. i. des. pclearbot.
              steps. gbase. eapply CIH. left. econs; et.
            }
          }
        - step. i. subst. apply simg_progress_flag.
          hexploit (K x_tgt). i. des. pclearbot.
          steps. gbase. eapply CIH. left. econs; et.
        - ired_both. steps.
        - des. force. exists x. steps. eapply IH; eauto.
        - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
        - steps. eapply IH; eauto.
          { unfold update. des_ifs. }
          { i. unfold update. des_ifs. et. }
        - steps. eapply IH; eauto.
        - steps.
        - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
        - des. force. exists x. steps. eapply IH; eauto.
        - steps. eapply IH; eauto.
          { unfold update. des_ifs. }
          { i. unfold update. des_ifs. et. }
        - steps. eapply IH; eauto.
        - eapply simg_progress_flag. gbase. eapply CIH.
          left. econs; eauto.
      }
      { destruct H. ides itr.
        { steps. }
        { steps. eapply simg_progress_flag. gbase. eapply CIH. right. econs; et. }
        rewrite <- ! bind_trigger. destruct e.
        { resub. destruct c. hexploit (fnsems_find_iff fn). i. des.
          { steps. rewrite NONE. unfold unwrapU, triggerUB. step. ss. }
          { inv SIM. steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
            guclo bindC_spec. econs.
            { eapply simg_progress_flag. gbase. eapply CIH.
              right. econs; ss. econs; et. }
            { i. ss. des. destruct vret_src, vret_tgt. des; clarify.
              steps. eapply simg_progress_flag.
              gbase. eapply CIH. right. econs; et. }
          }
          { inv SIM. hexploit (SIM0 (Some mn', args) (Some mn', args)); et. i. des.
            steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
            guclo bindC_spec. econs.
            { eapply simg_progress_flag. gbase. eapply CIH. left. econs; ss. et. }
            { i. ss. destruct vret_src, vret_tgt. des; clarify.
              steps. eapply simg_progress_flag. gbase. eapply CIH. right. econs; et.
              inv SIM. econs.
              { etrans; et. }
              { et. }
              { et. }
            }
          }
        }
        destruct s.
        { resub. destruct p.
          { steps. eapply simg_progress_flag.
            gbase. eapply CIH. right. econs; et.
            inv SIM. econs; et.
            { unfold update. des_ifs. }
            { ii. unfold update. des_ifs. et. }
          }
          { steps. eapply simg_progress_flag.
            gbase. eapply CIH. right.
            replace (st_tgt mn') with (st_src mn'); et.
            { econs; et. }
            { inv SIM. et. }
          }
        }
        { resub. destruct e.
          { steps. force. exists x. steps. eapply simg_progress_flag.
            gbase. eapply CIH; et. right. econs; et.
          }
          { steps. force. exists x. steps. eapply simg_progress_flag.
            gbase. eapply CIH; et. right. econs; et.
          }
          { steps. subst. eapply simg_progress_flag.
            gbase. eapply CIH; et. right. econs; et. }
        }
      }
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
      hexploit INIT. i. des. ginit.
      { eapply cpn7_wcompat; eauto with paco. }
      unfold ModSemL.initial_itr, assume.
      hexploit (fnsems_find_iff "main"). i. des.
      { steps. unshelve esplits; et. unfold ITree.map, unwrapU, triggerUB. steps.
        rewrite NONE. steps. ss. }
      { steps. unshelve esplits; et. unfold ITree.map, unwrapU. steps.
        rewrite SRC. rewrite TGT.
        steps. force. esplits; et. steps.
        guclo bindC_spec. econs.
        { eapply simg_progress_flag. gfinal. right. eapply sim_lift. right. econs; et. }
        { i. destruct vret_src, vret_tgt. des; clarify. steps. }
      }
      { inv H. hexploit (SIM (None, initial_arg) (None, initial_arg)); et. i. des.
        steps. force. esplits; et.
        steps. unfold ITree.map, unwrapU. steps.
        rewrite SRC. rewrite TGT. steps. guclo bindC_spec. econs.
        { eapply simg_flag_down. gfinal. right. eapply sim_lift. left. econs; et. }
        { i. destruct vret_src, vret_tgt. des; clarify. steps. }
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
        right. left. esplits; ss; et.
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
        destruct b. esplits; ss; et. erewrite alist_find_some_iff; et.
        { rewrite sim_mn. ss; et. }
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
