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

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.







Section SIM.

Context `{Σ: GRA.t}.

Section TY.
(* Context `{R: Type}. *)
Inductive _simg (simg: forall R (RR: R -> R -> Prop), Ord.t -> (itree eventE R) -> (itree eventE R) -> Prop)
          {R} (RR: R -> R -> Prop) (i0: Ord.t): (itree eventE R) -> (itree eventE R) -> Prop :=
| simg_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg simg RR i0 (Ret r_src) (Ret r_tgt)
| simg_syscall
    i1 ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: (eq ==> simg _ RR i1)%signature ktr_src0 ktr_tgt0)
  :
    _simg simg RR i0 (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)



| simg_tau
    i1 itr_src0 itr_tgt0
    (TAUBOTH: True)
    (* (ORD: Ordinal.le i1 i0) *)
    (SIM: simg _ RR i1 itr_src0 itr_tgt0)
  :
    _simg simg RR i0 (tau;; itr_src0) (tau;; itr_tgt0)
| simg_tauL
    i1 itr_src0 itr_tgt0
    (TAUL: True)
    (ORD: Ord.lt i1 i0)
    (SIM: simg _ RR i1 itr_src0 itr_tgt0)
  :
    _simg simg RR i0 (tau;; itr_src0) (itr_tgt0)
| simg_tauR
    i1 itr_src0 itr_tgt0
    (TAUR: True)
    (ORD: Ord.lt i1 i0)
    (SIM: simg _ RR i1 itr_src0 itr_tgt0)
  :
    _simg simg RR i0 (itr_src0) (tau;; itr_tgt0)



| simg_choose
    i1 X_src X_tgt ktr_src0 ktr_tgt0
    (CHOOSEBOTH: True)
    (* (ORD: Ordinal.le i1 i0) *)
    (SIM: forall x_tgt, exists x_src, simg _ RR i1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR i0 (trigger (Choose X_src) >>= ktr_src0) (trigger (Choose X_tgt) >>= ktr_tgt0)
| simg_chooseL
    i1 X ktr_src0 itr_tgt0
    (CHOOSEL: True)
    (ORD: Ord.lt i1 i0)
    (SIM: exists x, simg _ RR i1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR i0 (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_chooseR
    i1 X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (ORD: Ord.lt i1 i0)
    (SIM: forall x, simg _ RR i1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR i0 (itr_src0) (trigger (Choose X) >>= ktr_tgt0)



| simg_take
    i1 X_src X_tgt ktr_src0 ktr_tgt0
    (TAKEBOTH: True)
    (* (ORD: Ordinal.le i1 i0) *)
    (SIM: forall x_src, exists x_tgt, simg _ RR i1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR i0 (trigger (Take X_src) >>= ktr_src0) (trigger (Take X_tgt) >>= ktr_tgt0)
| simg_takeL
    i1 X ktr_src0 itr_tgt0
    (TAKEL: True)
    (ORD: Ord.lt i1 i0)
    (SIM: forall x, simg _ RR i1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR i0 (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_takeR
    i1 X itr_src0 ktr_tgt0
    (TAKER: True)
    (ORD: Ord.lt i1 i0)
    (SIM: exists x, simg _ RR i1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR i0 (itr_src0) (trigger (Take X) >>= ktr_tgt0)



(* | simg_stutter *)
(*     i1 itr_src itr_tgt *)
(*     (ORD: Ord.lt i1 i0) *)
(*     (SIM: simg _ RR i1 itr_src itr_tgt) *)
(*   : *)
(*     _simg simg RR i0 itr_src itr_tgt *)
.

Definition simg: forall R (RR: R -> R -> Prop), Ord.t -> (itree eventE R) -> (itree eventE R) -> Prop := paco5 _simg bot5.

Lemma simg_mon: monotone5 _simg.
Proof.
  ii. inv IN; try (by econs; et).
  - econs; et. ii. eapply LE; et.
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

Lemma simg_mon_ord r S SS i0 i1 (ORD: Ord.le i0 i1): @_simg r S SS i0 <2= @_simg r S SS i1.
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

















Global Program Instance _simg_refl r R RR `{Reflexive _ RR} (REFL: forall R RR `{Reflexive _ RR} o0, Reflexive (r R RR o0)) o0:
  Reflexive (@_simg r R RR o0).
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

Global Program Instance simg_paco_refl r R RR `{Reflexive _ RR} o0: Reflexive (paco5 _simg r R RR o0).
Next Obligation.
  revert_until Σ.
  pcofix CIH.
  i. pfold. eapply _simg_refl; et.
Qed.

Global Program Instance simg_gpaco_refl r R RR `{Reflexive _ RR} rg o0: Reflexive (gpaco5 _simg (cpn5 _simg) r rg R RR o0).
Next Obligation.
  gfinal. right. eapply simg_paco_refl; et.
Qed.

Global Program Instance simg_refl R RR `{Reflexive _ RR} o0: Reflexive (@simg R RR o0).
Next Obligation.
  eapply simg_paco_refl. ss.
Qed.






















Variant ordC (r: forall S (SS: S -> S -> Prop), Ord.t -> (itree eventE S) -> (itree eventE S) -> Prop):
  forall S (SS: S -> S -> Prop), Ord.t -> (itree eventE S) -> (itree eventE S) -> Prop :=
| ordC_intro
    o0 o1 R (RR: R -> R -> Prop) itr_src itr_tgt
    (ORD: Ord.le o0 o1)
    (SIM: r _ RR o0 itr_src itr_tgt)
  :
    ordC r RR o1 itr_src itr_tgt
.

Hint Constructors ordC: core.

Lemma ordC_mon
      r1 r2
      (LE: r1 <5= r2)
  :
    ordC r1 <5= ordC r2
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

Lemma ordC_prespectful: prespectful5 (_simg) ordC.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  rename x2 into o1. apply GF in SIM. pfold. inv SIM.
  - econs; eauto.
  - econs; eauto. ii. right. left. eapply SIM0; et.
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

Lemma ordC_spec: ordC <6= gupaco5 (_simg) (cpn5 _simg).
Proof. intros. eapply prespect5_uclo; eauto with paco. eapply ordC_prespectful. Qed.
(* Lemma ordC_spec2: ordC <6= gupaco5 (_simg) (cpn5 _simg). *)
(* Proof. intros. gclo. econs. { apply ordC_compatible. } eapply ordC_mon; try apply PR. ii. gbase. ss. Qed. *)











Variant bindR (r s: forall S (SS: S -> S -> Prop), Ord.t -> (itree eventE S) -> (itree eventE S) -> Prop):
  forall S (SS: S -> S -> Prop), Ord.t -> (itree eventE S) -> (itree eventE S) -> Prop :=
| bindR_intro
    o0 o1

    R RR
    (i_src i_tgt: itree eventE R)
    (SIM: r _ RR o0 i_src i_tgt)

    S SS
    (k_src k_tgt: ktree eventE R S)
    (SIMK: forall vret_src vret_tgt (SIM: RR vret_src vret_tgt), s _ SS o1 (k_src vret_src) (k_tgt vret_tgt))
  :
    (* bindR r s (Ordinal.add o0 o1) (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt) *)
    bindR r s SS (OrdArith.add o1 o0) (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

Hint Constructors bindR: core.

Lemma bindR_mon
      r1 r2 s1 s2
      (LEr: r1 <5= r2) (LEs: s1 <5= s2)
  :
    bindR r1 s1 <5= bindR r2 s2
.
Proof. ii. destruct PR; econs; et. Qed.

Definition bindC r := bindR r r.
Hint Unfold bindC: core.

(* Hint Resolve Ordinal.add_base_r: ord. *)
(* Hint Resolve Ordinal.add_base_l: ord. *)
(* Hint Resolve Ord.lt_le_lt: ord. *)
(* Hint Resolve Ordinal.le_lt_lt: ord. *)

(* Lemma bindC_wrespectful: prespectful5 (_simg) bindC. *)
Lemma bindC_wrespectful: wrespectful5 (_simg) bindC.
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

Lemma bindC_spec: bindC <6= gupaco5 (_simg) (cpn5 (_simg)).
Proof.
  intros. eapply wrespect5_uclo; eauto with paco. eapply bindC_wrespectful.
Qed.

Theorem simg_bind
        R S
        RR SS
        o0 (itr_src itr_tgt: itree eventE R)
        (SIM: simg RR o0 itr_src itr_tgt)
        o1 (ktr_src ktr_tgt: ktree eventE R S)
        (SIMK: forall vret_src vret_tgt (SIM: RR vret_src vret_tgt), simg SS o1 (ktr_src vret_src) (ktr_tgt vret_tgt))
  :
    simg SS (OrdArith.add o1 o0) (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt)
.
Proof.
  ginit.
  { eapply cpn5_wcompat; eauto with paco. }
  guclo bindC_spec. econs.
  - eauto with paco.
  - ii. exploit SIMK; eauto with paco.
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

Hypothesis (SIM: exists o0, simg eq o0 (ModSemL.initial_itr ms_src) (ModSemL.initial_itr ms_tgt)).

Theorem adequacy_global: Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_src).
Proof.
  revert SIM. i.
  admit "TODO".
Qed.

End SIM.

Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.
Hint Constructors ordC: core.
Hint Resolve ordC_mon: paco.
Hint Constructors bindR: core.
Hint Unfold bindC: core.
