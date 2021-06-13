Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
Require Import SimSTS.

Set Implicit Arguments.







Section SIM.

Context `{Σ: GRA.t}.

Section TY.
(* Context `{R: Type}. *)
Inductive _simg (simg: forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (i0: Ord.t): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg simg RR i0 (Ret r_src) (Ret r_tgt)
| simg_syscall
    i1 ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR i1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR i0 (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)



| simg_tau
    i1 itr_src0 itr_tgt0
    (TAUBOTH: True)
    (* (ORD: Ordinal.le i1 i0) *)
    (SIM: simg _ _ RR i1 itr_src0 itr_tgt0)
  :
    _simg simg RR i0 (tau;; itr_src0) (tau;; itr_tgt0)
| simg_tauL
    i1 itr_src0 itr_tgt0
    (TAUL: True)
    (ORD: Ord.lt i1 i0)
    (SIM: simg _ _ RR i1 itr_src0 itr_tgt0)
  :
    _simg simg RR i0 (tau;; itr_src0) (itr_tgt0)
| simg_tauR
    i1 itr_src0 itr_tgt0
    (TAUR: True)
    (ORD: Ord.lt i1 i0)
    (SIM: simg _ _ RR i1 itr_src0 itr_tgt0)
  :
    _simg simg RR i0 (itr_src0) (tau;; itr_tgt0)



| simg_choose
    i1 X_src X_tgt ktr_src0 ktr_tgt0
    (CHOOSEBOTH: True)
    (* (ORD: Ordinal.le i1 i0) *)
    (SIM: forall x_tgt, exists x_src, simg _ _ RR i1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR i0 (trigger (Choose X_src) >>= ktr_src0) (trigger (Choose X_tgt) >>= ktr_tgt0)
| simg_chooseL
    i1 X ktr_src0 itr_tgt0
    (CHOOSEL: True)
    (ORD: Ord.lt i1 i0)
    (SIM: exists x, simg _ _ RR i1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR i0 (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_chooseR
    i1 X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (ORD: Ord.lt i1 i0)
    (SIM: forall x, simg _ _ RR i1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR i0 (itr_src0) (trigger (Choose X) >>= ktr_tgt0)



| simg_take
    i1 X_src X_tgt ktr_src0 ktr_tgt0
    (TAKEBOTH: True)
    (* (ORD: Ordinal.le i1 i0) *)
    (SIM: forall x_src, exists x_tgt, simg _ _ RR i1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR i0 (trigger (Take X_src) >>= ktr_src0) (trigger (Take X_tgt) >>= ktr_tgt0)
| simg_takeL
    i1 X ktr_src0 itr_tgt0
    (TAKEL: True)
    (ORD: Ord.lt i1 i0)
    (SIM: forall x, simg _ _ RR i1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR i0 (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_takeR
    i1 X itr_src0 ktr_tgt0
    (TAKER: True)
    (ORD: Ord.lt i1 i0)
    (SIM: exists x, simg _ _ RR i1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR i0 (itr_src0) (trigger (Take X) >>= ktr_tgt0)



(* | simg_stutter *)
(*     i1 itr_src itr_tgt *)
(*     (ORD: Ord.lt i1 i0) *)
(*     (SIM: simg _ RR i1 itr_src itr_tgt) *)
(*   : *)
(*     _simg simg RR i0 itr_src itr_tgt *)
.

Definition simg: forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco6 _simg bot6.

Lemma simg_mon: monotone6 _simg.
Proof.
  ii. inv IN; try (by econs; et).
  - econs; et. ii. hexploit SIM; et. i; des. esplits; et.
  - des. econs; et.
  - econs; et. ii. hexploit SIM; et. i; des. esplits; et.
  - des. econs; et.
Qed.

(* Lemma simg_mon_ord r R RR o0 o1 (ORD: Ordinal.le o0 o1) (itr_src itr_tgt: itree eventE R): *)
(*   paco5 _simg r R RR o0 <2= paco5 _simg r R RR o1. *)
(* Proof. *)
(*   i. *)
(*   destruct (classic (Ord.lt o0 o1)). *)
(*   - pfold. econs; eauto. *)
(*   - *)
(* Qed. *)

Lemma simg_mon_ord r S0 S1 SS i0 i1 (ORD: Ord.le i0 i1): @_simg r S0 S1 SS i0 <2= @_simg r S0 S1 SS i1.
Proof.
  ii. inv PR; try (by econs; et).
  (* - econs; try apply SIM; et. etrans; et. *)
  - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
  - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
  (* - econs; try apply SIM; et. etrans; et. *)
  - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
  - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
  (* - econs; try apply SIM; et. etrans; et. *)
  - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
  - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
Qed.

(* Lemma simg_mon_rel r S SS SS' (LE: SS <2= SS') i0: @_simg r S SS i0 <2= @_simg r S SS' i0. *)
(* Proof. *)
(*   ii. inv PR; try (by econs; et). *)
(*   - econs; et. ii. hexploit (SIM _ _ H); et. i. eapply LE. ii. econs; try apply SIM. etrans; et. *)
(*   - econs; try apply SIM. eapply Ord.lt_le_lt; et. *)
(*   - econs; try apply SIM. eapply Ord.lt_le_lt; et. *)
(*   - econs; try apply SIM. etrans; et. *)
(*   - econs; try apply SIM. eapply Ord.lt_le_lt; et. *)
(*   - econs; try apply SIM. eapply Ord.lt_le_lt; et. *)
(*   - econs; try apply SIM. etrans; et. *)
(*   - econs; try apply SIM. eapply Ord.lt_le_lt; et. *)
(*   - econs; try apply SIM. eapply Ord.lt_le_lt; et. *)
(*   - econs; try apply SIM. eapply Ord.lt_le_lt; et. *)
(* Qed. *)

(* Lemma simg_mon_all r r' S SS SS' o o' (LEr: r <5= r') (LEss: SS <2= SS') (LEo: Ordinal.le o o'): *)
(*   @_simg r S SS o <2= @_simg r' S SS' o'. *)
(* Proof. *)
(*   ii. eapply simg_mon; et. eapply simg_mon_ord; et. *)

End TY.

Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.

















Global Program Instance _simg_refl
       (r : forall R0 R1, (R0 -> R1 -> Prop) -> Ord.t -> itree eventE R0 -> itree eventE R1 -> Prop)
       R RR `{Reflexive _ RR} (REFL: forall R RR `{Reflexive _ RR} o0, Reflexive (r R R RR o0)) o0:
  Reflexive (@_simg r R R RR o0).
Next Obligation.
  ides x.
  - econs; et.
  - econs; eauto; try refl.
  - destruct e.
    + rewrite <- ! bind_trigger. econs; et; try refl. ii. esplits; et. refl.
    + rewrite <- ! bind_trigger. econs; et; try refl. ii. esplits; et. refl.
    + rewrite <- ! bind_trigger. econs; et. ii. clarify. refl.
Unshelve.
  all: ss.
Qed.

Global Program Instance simg_paco_refl r R RR `{Reflexive _ RR} o0: Reflexive (paco6 _simg r R R RR o0).
Next Obligation.
  revert_until Σ.
  pcofix CIH.
  i. pfold. eapply _simg_refl; et.
Qed.

Global Program Instance simg_gpaco_refl r R RR `{Reflexive _ RR} rg o0: Reflexive (gpaco6 _simg (cpn6 _simg) r rg R R RR o0).
Next Obligation.
  gfinal. right. eapply simg_paco_refl; et.
Qed.

Global Program Instance simg_refl R RR `{Reflexive _ RR} o0: Reflexive (@simg R R RR o0).
Next Obligation.
  eapply simg_paco_refl. ss.
Qed.






















Variant ordC (r: forall S0 S1 (SS: S0 -> S1 -> Prop), Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: S0 -> S1 -> Prop), Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| ordC_intro
    o0 o1 R0 R1 (RR: R0 -> R1 -> Prop) itr_src itr_tgt
    (ORD: Ord.le o0 o1)
    (SIM: r _ _ RR o0 itr_src itr_tgt)
  :
    ordC r RR o1 itr_src itr_tgt
.

Hint Constructors ordC: core.

Lemma ordC_mon
      r1 r2
      (LE: r1 <6= r2)
  :
    ordC r1 <6= ordC r2
.
Proof. ii. destruct PR; econs; et. Qed.

Hint Resolve ordC_mon: paco.

(* Lemma ordC_prespectful: prespectful5 (_simg) ordC. *)
  (* wcompatible5 *)
(* Lemma ordC_compatible': compatible'5 (_simg) ordC. *)
(* Proof. *)
(*   econs; eauto with paco. *)
(*   ii. inv PR. csc. r in SIM. r. des. unfold id in *. esplits; et. *)
(*   rename x2 into o1. inv SIM0. *)
(*   - econs; eauto. *)
(*   - econs; eauto. ii. econs; try apply SIM1; et. refl. *)
(*   - econs; eauto. *)
(*   - econs; eauto. { eapply Ord.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. { eapply Ord.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. ii. spc SIM1. des. esplits; et. *)
(*   - econs; eauto. { eapply Ord.lt_le_lt; et. } des. esplits; et. econs; et. refl. *)
(*   - econs; eauto. { eapply Ord.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. ii. spc SIM1. des. esplits; et. *)
(*   - econs; eauto. { eapply Ord.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. { eapply Ord.lt_le_lt; et. } des. esplits; et. econs; et. refl. *)
(*   - econs. { eapply Ord.lt_le_lt; et. } econs; et. refl. *)
(* Qed. *)

(* Lemma ordC_compatible: compatible5 (_simg) ordC. *)
(* Proof. *)
(*   econs; eauto with paco. *)
(*   ii. inv PR. csc. *)
(*   rename x2 into o1. inv SIM. *)
(*   - econs; eauto. *)
(*   - econs; eauto. ii. econs; try apply SIM0; et. refl. *)
(*   - econs; eauto. econs; eauto with paco. *)
(*   - econs; eauto. { eapply Ord.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. { eapply Ord.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. ii. spc SIM0. des. esplits; et. *)
(*   - econs; eauto. { eapply Ord.lt_le_lt; et. } des. esplits; et. econs; et. refl. *)
(*   - econs; eauto. { eapply Ord.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. ii. spc SIM0. des. esplits; et. *)
(*   - econs; eauto. { eapply Ord.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. { eapply Ord.lt_le_lt; et. } des. esplits; et. econs; et. refl. *)
(* Qed. *)

Lemma ordC_prespectful: prespectful6 (_simg) ordC.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  rename x2 into o1. apply GF in SIM. pfold. inv SIM.
  - econs; eauto.
  - econs; eauto.
  - econs; eauto.
  - econs; eauto. { eapply Ord.lt_le_lt; et. }
  - econs; eauto. { eapply Ord.lt_le_lt; et. }
  - econs; eauto. ii. spc SIM0. des. esplits; et.
  - econs; eauto. { eapply Ord.lt_le_lt; et. } des. esplits; et.
  - econs; eauto. { eapply Ord.lt_le_lt; et. }
  - econs; eauto. ii. spc SIM0. des. esplits; et.
  - econs; eauto. { eapply Ord.lt_le_lt; et. }
  - econs; eauto. { eapply Ord.lt_le_lt; et. } des. esplits; et.
  (* - econs. { eapply Ord.lt_le_lt; et. } right. left. et. *)
Qed.

Lemma ordC_spec: ordC <7= gupaco6 (_simg) (cpn6 _simg).
Proof. intros. eapply prespect6_uclo; eauto with paco. eapply ordC_prespectful. Qed.
(* Lemma ordC_spec2: ordC <6= gupaco5 (_simg) (cpn5 _simg). *)
(* Proof. intros. gclo. econs. { apply ordC_compatible. } eapply ordC_mon; try apply PR. ii. gbase. ss. Qed. *)











Variant bindR (r s: forall S0 S1 (SS: S0 -> S1 -> Prop), Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: S0 -> S1 -> Prop), Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| bindR_intro
    o0 o1

    R0 R1 RR
    (i_src: itree eventE R0) (i_tgt: itree eventE R1)
    (SIM: r _ _ RR o0 i_src i_tgt)

    S0 S1 SS
    (k_src: ktree eventE R0 S0) (k_tgt: ktree eventE R1 S1)
    (SIMK: forall vret_src vret_tgt (SIM: RR vret_src vret_tgt), s _ _ SS o1 (k_src vret_src) (k_tgt vret_tgt))
  :
    (* bindR r s (Ordinal.add o0 o1) (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt) *)
    bindR r s SS (OrdArith.add o1 o0) (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

Hint Constructors bindR: core.

Lemma bindR_mon
      r1 r2 s1 s2
      (LEr: r1 <6= r2) (LEs: s1 <6= s2)
  :
    bindR r1 s1 <6= bindR r2 s2
.
Proof. ii. destruct PR; econs; et. Qed.

Definition bindC r := bindR r r.
Hint Unfold bindC: core.

(* Hint Resolve Ordinal.add_base_r: ord. *)
(* Hint Resolve Ordinal.add_base_l: ord. *)
(* Hint Resolve Ord.lt_le_lt: ord. *)
(* Hint Resolve Ordinal.le_lt_lt: ord. *)

(* Lemma bindC_wrespectful: prespectful5 (_simg) bindC. *)
Lemma bindC_wrespectful: wrespectful6 (_simg) bindC.
Proof.
  econstructor; repeat intro.
  { eapply bindR_mon; eauto. }
  rename l into llll.
  eapply bindR_mon in PR; cycle 1.
  { eapply GF. }
  { i. eapply PR0. }
  inv PR. csc. inv SIM.
  + irw.
    exploit SIMK; eauto. i.
    eapply simg_mon_ord.
    { instantiate (1:=o1). eapply OrdArith.add_base_l. }
    eapply simg_mon; eauto with paco.
  + rewrite ! bind_bind. econs; eauto. ii.
    { econs 2; eauto with paco. econs; eauto with paco. }


  + irw. econs; eauto.
    (* { eapply Ordinal.add_le_r; et. } *)
    { econs 2; eauto with paco. econs; eauto with paco. }
  + rewrite ! bind_tau. econs; eauto.
    { instantiate (1:= OrdArith.add o1 i1). eapply OrdArith.lt_add_r; et. }
    econs 2; eauto with paco. econs; eauto with paco.
  + irw. econs; eauto.
    { instantiate (1:= OrdArith.add o1 i1). eapply OrdArith.lt_add_r; et. }
    econs 2; eauto with paco. econs; eauto with paco.


  + rewrite ! bind_bind. econs; eauto.
    (* { eapply Ordinal.add_le_r; et. } *)
    { ii. spc SIM0. des. esplits; et. econs 2; eauto with paco. econs; eauto with paco. }
  + rewrite ! bind_bind. econs; eauto.
    { instantiate (1:= OrdArith.add o1 i1). eapply OrdArith.lt_add_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.
  + rewrite ! bind_bind. econs; eauto.
    { instantiate (1:= OrdArith.add o1 i1). eapply OrdArith.lt_add_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.

  + rewrite ! bind_bind. econs; eauto.
    (* { eapply Ordinal.add_le_r; et. } *)
    { ii. spc SIM0. des. esplits; et. econs 2; eauto with paco. econs; eauto with paco. }
  + rewrite ! bind_bind. econs; eauto.
    { instantiate (1:= OrdArith.add o1 i1). eapply OrdArith.lt_add_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.
  + rewrite ! bind_bind. econs; eauto.
    { instantiate (1:= OrdArith.add o1 i1). eapply OrdArith.lt_add_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.
Qed.

Lemma bindC_spec: bindC <7= gupaco6 (_simg) (cpn6 (_simg)).
Proof.
  intros. eapply wrespect6_uclo; eauto with paco. eapply bindC_wrespectful.
Qed.

Theorem simg_bind
        R0 R1 S0 S1
        RR SS
        o0 (itr_src: itree eventE R0) (itr_tgt: itree eventE R1)
        (SIM: simg RR o0 itr_src itr_tgt)
        o1 (ktr_src: ktree eventE R0 S0) (ktr_tgt: ktree eventE R1 S1)
        (SIMK: forall vret_src vret_tgt (SIM: RR vret_src vret_tgt), simg SS o1 (ktr_src vret_src) (ktr_tgt vret_tgt))
  :
    simg SS (OrdArith.add o1 o0) (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt)
.
Proof.
  ginit.
  { eapply cpn6_wcompat; eauto with paco. }
  guclo bindC_spec. econs.
  - eauto with paco.
  - ii. exploit SIMK; eauto with paco.
Qed.



Lemma step_trigger_choose_iff X k itr e
      (STEP: ModSemL.step (trigger (Choose X) >>= k) e itr)
  :
    exists x,
      e = None /\ itr = k x.
Proof.
  inv STEP.
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss.
    unfold trigger in H0. ss. cbn in H0.
    dependent destruction H0. ired. et.  }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
Qed.

Lemma step_trigger_take_iff X k itr e
      (STEP: ModSemL.step (trigger (Take X) >>= k) e itr)
  :
    exists x,
      e = None /\ itr = k x.
Proof.
  inv STEP.
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss.
    unfold trigger in H0. ss. cbn in H0.
    dependent destruction H0. ired. et.  }
  { eapply f_equal with (f:=observe) in H0. ss. }
Qed.

Lemma step_tau_iff itr0 itr1 e
      (STEP: ModSemL.step (Tau itr0) e itr1)
  :
    e = None /\ itr0 = itr1.
Proof.
  inv STEP. et.
Qed.

Lemma step_ret_iff rv itr e
      (STEP: ModSemL.step (Ret rv) e itr)
  :
    False.
Proof.
  inv STEP.
Qed.

Lemma step_trigger_syscall_iff fn args rvs k e itr
      (STEP: ModSemL.step (trigger (Syscall fn args rvs) >>= k) e itr)
  :
    exists rv, itr = k rv /\ e = Some (event_sys fn args rv)
               /\ <<RV: rvs rv>> /\ <<SYS: syscall_sem (event_sys fn args rv)>>.
Proof.
  inv STEP.
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss.
    unfold trigger in H0. ss. cbn in H0.
    dependent destruction H0. ired. et. }
Qed.


Let itree_eta E R (itr0 itr1: itree E R)
    (OBSERVE: observe itr0 = observe itr1)
  :
    itr0 = itr1.
Proof.
  rewrite (itree_eta_ itr0).
  rewrite (itree_eta_ itr1).
  rewrite OBSERVE. auto.
Qed.

Lemma step_trigger_choose X k x
  :
    ModSemL.step (trigger (Choose X) >>= k) None (k x).
Proof.
  unfold trigger. ss.
  match goal with
  | [ |- ModSemL.step ?itr _ _] =>
    replace itr with (Subevent.vis (Choose X) k)
  end; ss.
  { econs. }
  { eapply itree_eta. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta. ss. }
Qed.

Lemma step_trigger_take X k x
  :
    ModSemL.step (trigger (Take X) >>= k) None (k x).
Proof.
  unfold trigger. ss.
  match goal with
  | [ |- ModSemL.step ?itr _ _] =>
    replace itr with (Subevent.vis (Take X) k)
  end; ss.
  { econs. }
  { eapply itree_eta. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta. ss. }
Qed.

Lemma step_trigger_syscall fn args (rvs: val -> Prop) k rv
      (RV: rvs rv) (SYS: syscall_sem (event_sys fn args rv))
  :
    ModSemL.step (trigger (Syscall fn args rvs) >>= k) (Some (event_sys fn args rv)) (k rv).
Proof.
  unfold trigger. ss.
  match goal with
  | [ |- ModSemL.step ?itr _ _] =>
    replace itr with (Subevent.vis (Syscall fn args rvs) k)
  end; ss.
  { econs; et. }
  { eapply itree_eta. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta. ss. }
Qed.

Lemma step_tau itr
  :
    ModSemL.step (Tau itr) None itr.
Proof.
  econs.
Qed.

Theorem adequacy_global_itree itr_src itr_tgt
        (SIM: exists o0, simg eq o0 itr_src itr_tgt)
  :
    Beh.of_program (ModSemL.compile_itree itr_tgt)
    <1=
    Beh.of_program (ModSemL.compile_itree itr_src).
Proof.
  unfold Beh.of_program. ss.
  i. destruct SIM as [o SIMG]. eapply adequacy_aux; et.
  { eapply Ord.lt_well_founded. }
  instantiate (1:=o). clear x0 PR.
  generalize itr_tgt at 1 as md_tgt.
  generalize itr_src at 1 as md_src. i.
  revert o itr_src itr_tgt SIMG. pcofix CIH.
  i. punfold SIMG. inv SIMG; pfold.
  { destruct (classic (exists rv, @Any.downcast val r_tgt = Some (Vint rv) /\
                                  (0 <=? rv)%Z && (rv <? two_power_nat 32)%Z)).
    { des. eapply sim_fin; ss.
      { cbn. rewrite H. rewrite H0. ss. }
      { cbn. rewrite H. rewrite H0. ss. }
    }
    { eapply sim_angelic_both.
      { cbn. des_ifs. exfalso. eapply H. et. }
      { cbn. des_ifs. exfalso. eapply H. et. }
      i. exfalso. inv STEP.
    }
  }
  { eapply sim_vis; ss. i.
    eapply step_trigger_syscall_iff in STEP. des. clarify.
    esplits.
    { eapply step_trigger_syscall; et. }
    { right. eapply CIH.
      hexploit SIM; et. i. pclearbot. eapply H. }
  }
  { eapply sim_demonic_both; ss. i.
    eapply step_tau_iff in STEP. des. clarify.
    esplits.
    { eapply step_tau; et. }
    { right. eapply CIH. destruct SIM; ss. apply p. }
  }
  { eapply sim_demonic_src; ss.
    esplits.
    { eapply step_tau; et. }
    { et. }
    { right. eapply CIH. destruct SIM; ss. }
  }
  { eapply sim_demonic_tgt; ss. i.
    eapply step_tau_iff in STEP. des. clarify.
    esplits.
    { et. }
    { right. eapply CIH. destruct SIM; ss. }
  }
  { eapply sim_demonic_both; ss. i.
    eapply step_trigger_choose_iff in STEP. des. clarify.
    hexploit (SIM x); et. i. des.
    esplits.
    { eapply step_trigger_choose; et. }
    { right. eapply CIH. destruct H; ss. apply p. }
  }
  { eapply sim_demonic_src; ss. destruct SIM.
    esplits.
    { eapply step_trigger_choose; et. }
    { et. }
    { right. eapply CIH. destruct H; ss. apply p. }
  }
  { eapply sim_demonic_tgt; ss. i.
    eapply step_trigger_choose_iff in STEP. des. clarify.
    hexploit (SIM x); et. i. des.
    esplits.
    { et. }
    { right. eapply CIH. destruct H; ss. }
  }
  { eapply sim_angelic_both; ss. i.
    eapply step_trigger_take_iff in STEP. des. clarify.
    hexploit (SIM x); et. i. des.
    esplits.
    { eapply step_trigger_take; et. }
    { right. eapply CIH. destruct H; ss. apply p. }
  }
  { eapply sim_angelic_src; ss. i.
    eapply step_trigger_take_iff in STEP. des. clarify.
    hexploit (SIM x); et. i. des.
    esplits.
    { et. }
    { right. eapply CIH. destruct H; ss. }
  }
  { eapply sim_angelic_tgt; ss. destruct SIM.
    esplits.
    { eapply step_trigger_take; et. }
    { et. }
    { right. eapply CIH. destruct H; ss. apply p. }
  }
Qed.


Variable md_src md_tgt: ModL.t.
Let ms_src: ModSemL.t := md_src.(ModL.enclose).
Let ms_tgt: ModSemL.t := md_tgt.(ModL.enclose).
(* Let sim_fnsem: relation (string * (list val -> itree Es val)) := *)
(*   fun '(fn_src, fsem_src) '(fn_tgt, fsem_tgt) => *)
(*     (<<NAME: fn_src = fn_tgt>>) /\ *)
(*     (<<SEM: forall varg, exists itr_src itr_tgt, *)
(*           (<<SRC: fsem_src varg = resum_itr itr_src>>) /\ *)
(*           (<<TGT: fsem_tgt varg = resum_itr itr_tgt>>) /\ *)
(*           (<<SIM: exists i0, simg i0 itr_src itr_tgt>>)>>) *)
(* . *)
(* Hypothesis (SIM: Forall2 sim_fnsem ms_src.(ModSemL.fnsems) ms_tgt.(ModSemL.fnsems)). *)

Hypothesis (SIM: exists o0, simg eq o0 (ModSemL.initial_itr ms_src (Some (ModL.wf md_src))) (ModSemL.initial_itr ms_tgt (Some (ModL.wf md_tgt)))).


Local Hint Resolve cpn3_wcompat: paco.


Theorem adequacy_global: Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_src).
Proof.
  eapply adequacy_global_itree. eapply SIM.
Qed.

End SIM.

Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.
Hint Constructors ordC: core.
Hint Resolve ordC_mon: paco.
Hint Constructors bindR: core.
Hint Unfold bindC: core.
