Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
Require Import SimSTSdouble.

Set Implicit Arguments.







Section SIM.

Section TY.
(* Context `{R: Type}. *)
Inductive _simg (simg: forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (i_src0 i_tgt0: Ord.t): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg simg RR i_src0 i_tgt0 (Ret r_src) (Ret r_tgt)
| simg_syscall
    i_src1 i_tgt1 ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR i_src1 i_tgt1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR i_src0 i_tgt0 (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)


| simg_tauL
    i_src1 i_tgt1 itr_src0 itr_tgt0
    (TAUL: True)
    (ORD: Ord.lt i_tgt1 i_tgt0)
    (SIM: simg _ _ RR i_src1 i_tgt1 itr_src0 itr_tgt0)
  :
    _simg simg RR i_src0 i_tgt0 (tau;; itr_src0) (itr_tgt0)
| simg_tauR
    i_src1 i_tgt1 itr_src0 itr_tgt0
    (TAUR: True)
    (ORD: Ord.lt i_src1 i_src0)
    (SIM: simg _ _ RR i_src1 i_tgt1 itr_src0 itr_tgt0)
  :
    _simg simg RR i_src0 i_tgt0 (itr_src0) (tau;; itr_tgt0)


| simg_chooseL
    i_src1 i_tgt1 X ktr_src0 itr_tgt0
    (CHOOSEL: True)
    (ORD: Ord.lt i_tgt1 i_tgt0)
    (SIM: exists x, simg _ _ RR i_src1 i_tgt1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR i_src0 i_tgt0 (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_chooseR
    i_src1 i_tgt1 X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (ORD: Ord.lt i_src1 i_src0)
    (SIM: forall x, simg _ _ RR i_src1 i_tgt1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR i_src0 i_tgt0 (itr_src0) (trigger (Choose X) >>= ktr_tgt0)


| simg_takeL
    i_src1 i_tgt1 X ktr_src0 itr_tgt0
    (TAKEL: True)
    (ORD: Ord.lt i_tgt1 i_tgt0)
    (SIM: forall x, simg _ _ RR i_src1 i_tgt1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR i_src0 i_tgt0 (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_takeR
    i_src1 i_tgt1 X itr_src0 ktr_tgt0
    (TAKER: True)
    (ORD: Ord.lt i_src1 i_src0)
    (SIM: exists x, simg _ _ RR i_src1 i_tgt1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR i_src0 i_tgt0 (itr_src0) (trigger (Take X) >>= ktr_tgt0)
.

Definition simg: forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco7 _simg bot7.

Lemma simg_mon: monotone7 _simg.
Proof.
  ii. inv IN; try (by econs; et).
  - econs; et. ii. hexploit SIM; et. i; des. esplits; et.
  - des. econs; et.
Qed.

Lemma simg_mon_ord r S0 S1 SS i_src0 i_src1 i_tgt0 i_tgt1
      (ORDSRC: Ord.le i_src0 i_src1) (ORDTGT: Ord.le i_tgt0 i_tgt1):
  @_simg r S0 S1 SS i_src0 i_tgt0 <2= @_simg r S0 S1 SS i_src1 i_tgt1.
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


End TY.

Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.

















Global Program Instance simg_paco_refl r R RR `{Reflexive _ RR} o_src0 o_tgt0
       (LT: Ord.lt Ord.O o_src0 /\ Ord.lt Ord.O o_tgt0)
  : Reflexive (paco7 _simg r R R RR o_src0 o_tgt0).
Next Obligation.
  revert_until r. pcofix CIH. i. pfold. ides x.
  - econs; et.
  - econs 3; et. left. pfold. econs 4; auto.
    { eapply Ord.S_lt. }
    right. et.
  - rewrite <- ! bind_trigger. destruct e.
    + econs 6; et. i. left. pfold. econs 5; auto.
      { eapply Ord.S_lt. }
      esplits. right. et.
    + econs 7; et. i. left. pfold. econs 8; auto.
      { eapply Ord.S_lt. }
      esplits. right. et.
    + econs; et. i. subst. right. et.
Qed.

Global Program Instance simg_gpaco_refl r R RR `{Reflexive _ RR} rg o_src0 o_tgt0
       (LT: Ord.lt Ord.O o_src0 /\ Ord.lt Ord.O o_tgt0)
  : Reflexive (gpaco7 _simg (cpn7 _simg) r rg R R RR o_src0 o_tgt0).
Next Obligation.
  gfinal. right. eapply simg_paco_refl; et.
Qed.

Global Program Instance simg_refl R RR `{Reflexive _ RR} o_src0 o_tgt0
       (LT: Ord.lt Ord.O o_src0 /\ Ord.lt Ord.O o_tgt0)
  : Reflexive (@simg R R RR o_src0 o_tgt0).
Next Obligation.
  eapply simg_paco_refl; ss.
Qed.






















Variant ordC (r: forall S0 S1 (SS: S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| ordC_intro
    o_src0 o_src1 o_tgt0 o_tgt1 R0 R1 (RR: R0 -> R1 -> Prop) itr_src itr_tgt
    (ORDSRC: Ord.le o_src0 o_src1)
    (ORDTGT: Ord.le o_tgt0 o_tgt1)
    (SIM: r _ _ RR o_src0 o_tgt0 itr_src itr_tgt)
  :
    ordC r RR o_src1 o_tgt1 itr_src itr_tgt
.
Hint Constructors ordC: core.

Lemma ordC_mon
      r1 r2
      (LE: r1 <7= r2)
  :
    ordC r1 <7= ordC r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve ordC_mon: paco.

Lemma ordC_prespectful: prespectful7 (_simg) ordC.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  rename x2 into o1. apply GF in SIM. pfold. inv SIM.
  - econs; eauto.
  - econs; eauto.
  - econs; eauto. { eapply Ord.lt_le_lt; et. }
  - econs; eauto. { eapply Ord.lt_le_lt; et. }
  - econs; eauto. { eapply Ord.lt_le_lt; et. } des. esplits; et.
  - econs; eauto. { eapply Ord.lt_le_lt; et. }
  - econs; eauto. { eapply Ord.lt_le_lt; et. }
  - econs; eauto. { eapply Ord.lt_le_lt; et. } des. esplits; et.
Qed.

Lemma ordC_spec: ordC <8= gupaco7 (_simg) (cpn7 _simg).
Proof. intros. eapply prespect7_uclo; eauto with paco. eapply ordC_prespectful. Qed.











Variant bindR (r s: forall S0 S1 (SS: S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| bindR_intro
    o_src0 o_src1 o_tgt0 o_tgt1

    R0 R1 RR
    (i_src: itree eventE R0) (i_tgt: itree eventE R1)
    (SIM: r _ _ RR o_src0 o_tgt0 i_src i_tgt)

    S0 S1 SS
    (k_src: ktree eventE R0 S0) (k_tgt: ktree eventE R1 S1)
    (SIMK: forall vret_src vret_tgt (SIM: RR vret_src vret_tgt), s _ _ SS o_src1 o_tgt1 (k_src vret_src) (k_tgt vret_tgt))
  :
    (* bindR r s (Ordinal.add o0 o1) (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt) *)
    bindR r s SS (OrdArith.add o_src1 o_src0) (OrdArith.add o_tgt1 o_tgt0) (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

Hint Constructors bindR: core.

Lemma bindR_mon
      r1 r2 s1 s2
      (LEr: r1 <7= r2) (LEs: s1 <7= s2)
  :
    bindR r1 s1 <7= bindR r2 s2
.
Proof. ii. destruct PR; econs; et. Qed.

Definition bindC r := bindR r r.
Hint Unfold bindC: core.

Lemma bindC_wrespectful: wrespectful7 (_simg) bindC.
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
    { eapply OrdArith.add_base_l. }
    { eapply OrdArith.add_base_l. }
    eapply simg_mon; eauto with paco.
  + rewrite ! bind_bind. econs; eauto. ii.
    { econs 2; eauto with paco. econs; eauto with paco. }

  + rewrite ! bind_tau. econs; eauto.
    { eapply OrdArith.lt_add_r; et. }
    econs 2; eauto with paco. econs; eauto with paco.
  + irw. econs; eauto.
    { eapply OrdArith.lt_add_r; et. }
    econs 2; eauto with paco. econs; eauto with paco.

  + rewrite ! bind_bind. econs; eauto.
    { eapply OrdArith.lt_add_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.
  + rewrite ! bind_bind. econs; eauto.
    { eapply OrdArith.lt_add_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.

  + rewrite ! bind_bind. econs; eauto.
    { eapply OrdArith.lt_add_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.
  + rewrite ! bind_bind. econs; eauto.
    { eapply OrdArith.lt_add_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.
Qed.

Lemma bindC_spec: bindC <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply wrespect7_uclo; eauto with paco. eapply bindC_wrespectful.
Qed.

Theorem simg_bind
        R0 R1 S0 S1
        RR SS
        o_src0 o_tgt0 (itr_src: itree eventE R0) (itr_tgt: itree eventE R1)
        (SIM: simg RR o_src0 o_tgt0 itr_src itr_tgt)
        o_src1 o_tgt1 (ktr_src: ktree eventE R0 S0) (ktr_tgt: ktree eventE R1 S1)
        (SIMK: forall vret_src vret_tgt (SIM: RR vret_src vret_tgt), simg SS o_src1 o_tgt1 (ktr_src vret_src) (ktr_tgt vret_tgt))
  :
    simg SS (OrdArith.add o_src1 o_src0) (OrdArith.add o_tgt1 o_tgt0)
         (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt)
.
Proof.
  ginit.
  { eapply cpn7_wcompat; eauto with paco. }
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


Lemma itree_eta_eq E R (itr0 itr1: itree E R)
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
  { eapply itree_eta_eq. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta_eq. ss. }
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
  { eapply itree_eta_eq. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta_eq. ss. }
Qed.

Lemma step_trigger_syscall fn args (rvs: Any.t -> Prop) k rv
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
  { eapply itree_eta_eq. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta_eq. ss. }
Qed.

Lemma step_tau itr
  :
    ModSemL.step (Tau itr) None itr.
Proof.
  econs.
Qed.

Context {CONFS CONFT: EMSConfig}.
Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

Theorem adequacy_global_itree itr_src itr_tgt
        (SIM: exists o_src0 o_tgt0, simg eq o_src0 o_tgt0 itr_src itr_tgt)
  :
    Beh.of_program (@ModSemL.compile_itree CONFT itr_tgt)
    <1=
    Beh.of_program (@ModSemL.compile_itree CONFS itr_src).
Proof.
  unfold Beh.of_program. ss.
  i. destruct SIM as [o_src0 [o_tgt0 SIMG]]. eapply adequacy_aux; et.
  { eapply Ord.lt_well_founded. }
  { eapply Ord.lt_well_founded. }
  instantiate (1:=o_tgt0). instantiate (1:=o_src0). clear x0 PR.
  generalize itr_tgt at 1 as md_tgt.
  generalize itr_src at 1 as md_src. i.
  revert o_src0 o_tgt0 itr_src itr_tgt SIMG. pcofix CIH.
  i. punfold SIMG. inv SIMG; pfold.
  { destruct (finalize r_tgt) eqn:T.
    { eapply sim_fin; ss; cbn; des_ifs; rewrite FINSAME in *; clarify. }
    { eapply sim_angelic_src.
      { cbn. des_ifs; rewrite FINSAME in *; clarify. }
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
  { eapply sim_demonic_src; ss.
    esplits.
    { eapply step_tau; et. }
    { et. }
    { right. eapply CIH. destruct SIM; ss. et. }
  }
  { eapply sim_demonic_tgt; ss. i.
    eapply step_tau_iff in STEP. des. clarify.
    esplits.
    { et. }
    { right. eapply CIH. destruct SIM; ss. et. }
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
    { right. eapply CIH. destruct H; ss. et. }
  }
  { eapply sim_angelic_src; ss. i.
    eapply step_trigger_take_iff in STEP. des. clarify.
    hexploit (SIM x); et. i. des.
    esplits.
    { et. }
    { right. eapply CIH. destruct H; ss. et. }
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

Section ADEQUACY.
Hypothesis (SIM: exists o_src0 o_tgt0, simg eq o_src0 o_tgt0 (@ModSemL.initial_itr ms_src CONFS (Some (ModL.wf md_src))) (@ModSemL.initial_itr ms_tgt CONFT (Some (ModL.wf md_tgt)))).


Theorem adequacy_global: Beh.of_program (@ModL.compile _ CONFT md_tgt) <1= Beh.of_program (@ModL.compile _ CONFS md_src).
Proof.
  eapply adequacy_global_itree. eapply SIM.
Qed.
End ADEQUACY.
End SIM.

Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.
Hint Constructors ordC: core.
Hint Resolve ordC_mon: paco.
Hint Constructors bindR: core.
Hint Unfold bindC: core.


Inductive _simg_safe (simg: forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (i_src0 i_tgt0: Ord.t): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_safe_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg_safe simg RR i_src0 i_tgt0 (Ret r_src) (Ret r_tgt)
| simg_safe_syscall
    i_src1 i_tgt1 ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR i_src1 i_tgt1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg_safe simg RR i_src0 i_tgt0 (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)


| simg_safe_tauL
    i_src1 i_tgt1 itr_src0 itr_tgt0
    (TAUL: True)
    (ORD: Ord.lt i_tgt1 i_tgt0)
    (SIM: simg _ _ RR i_src1 i_tgt1 itr_src0 itr_tgt0)
  :
    _simg_safe simg RR i_src0 i_tgt0 (tau;; itr_src0) (itr_tgt0)
| simg_safe_tauR
    i_src1 i_tgt1 itr_src0 itr_tgt0
    (TAUR: True)
    (ORD: Ord.lt i_src1 i_src0)
    (SIM: simg _ _ RR i_src1 i_tgt1 itr_src0 itr_tgt0)
  :
    _simg_safe simg RR i_src0 i_tgt0 (itr_src0) (tau;; itr_tgt0)


| simg_safe_chooseR
    i_src1 i_tgt1 X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (ORD: Ord.lt i_src1 i_src0)
    (SIM: forall x, simg _ _ RR i_src1 i_tgt1 itr_src0 (ktr_tgt0 x))
  :
    _simg_safe simg RR i_src0 i_tgt0 (itr_src0) (trigger (Choose X) >>= ktr_tgt0)


| simg_safe_takeL
    i_src1 i_tgt1 X ktr_src0 itr_tgt0
    (TAKEL: True)
    (ORD: Ord.lt i_tgt1 i_tgt0)
    (SIM: forall x, simg _ _ RR i_src1 i_tgt1 (ktr_src0 x) itr_tgt0)
  :
    _simg_safe simg RR i_src0 i_tgt0 (trigger (Take X) >>= ktr_src0) (itr_tgt0)
.

Lemma simg_safe_spec:
  _simg_safe <8= _simg.
Proof. i. inv PR; try by (econs; eauto). Qed.
