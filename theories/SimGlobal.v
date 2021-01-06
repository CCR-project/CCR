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
Require Import Ordinal ClassicalOrdinal.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.




Lemma ind2
      (P: Ordinal.t -> Prop)
      (SUCC: forall o s (SUCC: Ordinal.is_S o s) (IH: P o)
                    (HELPER: forall o' (LT: Ordinal.lt o' s), P o'), P s)
      (LIMIT: forall A (os: A -> Ordinal.t) o (JOIN: Ordinal.is_join os o)
                     (OPEN: Ordinal.open os)
                     (IH: forall a, P (os a))
                     (HELPER: forall o' (LT: Ordinal.lt o' o), P o'), P o)
  :
    forall o, P o.
Proof.
  eapply well_founded_induction.
  { eapply Ordinal.lt_well_founded. }
  i. destruct (ClassicalOrdinal.limit_or_S x).
  - des. eapply SUCC; eauto. eapply H. eapply H0.
  - des. eapply LIMIT; eauto. i. eapply H.
    specialize (H1 a). des. eapply Ordinal.lt_le_lt; eauto. eapply H0.
Qed.




Section SIM.

Context `{Σ: GRA.t}.

Section TY.
(* Context `{R: Type}. *)
Inductive _simg (simg: forall R (RR: R -> R -> Prop), Ordinal.t -> (itree eventE R) -> (itree eventE R) -> Prop)
          {R} (RR: R -> R -> Prop) (i0: Ordinal.t): (itree eventE R) -> (itree eventE R) -> Prop :=
| simg_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg simg RR i0 (Ret r_src) (Ret r_tgt)
| simg_syscall
    i1 ktr_src0 ktr_tgt0 fn m0 varg
    (SIM: (eq ==> simg _ RR i1)%signature ktr_src0 ktr_tgt0)
  :
    _simg simg RR i0 (trigger (Syscall fn m0 varg) >>= ktr_src0) (trigger (Syscall fn m0 varg) >>= ktr_tgt0)



| simg_tau
    i1 itr_src0 itr_tgt0
    (TAUBOTH: True)
    (ORD: Ordinal.le i1 i0)
    (SIM: simg _ RR i1 itr_src0 itr_tgt0)
  :
    _simg simg RR i0 (tau;; itr_src0) (tau;; itr_tgt0)
| simg_tauL
    i1 itr_src0 itr_tgt0
    (TAUL: True)
    (ORD: Ordinal.lt i1 i0)
    (SIM: simg _ RR i1 itr_src0 itr_tgt0)
  :
    _simg simg RR i0 (tau;; itr_src0) (itr_tgt0)
| simg_tauR
    i1 itr_src0 itr_tgt0
    (TAUR: True)
    (ORD: Ordinal.lt i1 i0)
    (SIM: simg _ RR i1 itr_src0 itr_tgt0)
  :
    _simg simg RR i0 (itr_src0) (tau;; itr_tgt0)



| simg_choose
    i1 X_src X_tgt ktr_src0 ktr_tgt0
    (CHOOSEBOTH: True)
    (ORD: Ordinal.le i1 i0)
    (SIM: forall x_tgt, exists x_src, simg _ RR i1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR i0 (trigger (Choose X_src) >>= ktr_src0) (trigger (Choose X_tgt) >>= ktr_tgt0)
| simg_chooseL
    i1 X ktr_src0 itr_tgt0
    (CHOOSEL: True)
    (ORD: Ordinal.lt i1 i0)
    (SIM: exists x, simg _ RR i1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR i0 (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_chooseR
    i1 X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (ORD: Ordinal.lt i1 i0)
    (SIM: forall x, simg _ RR i1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR i0 (itr_src0) (trigger (Choose X) >>= ktr_tgt0)



| simg_take
    i1 X_src X_tgt ktr_src0 ktr_tgt0
    (TAKEBOTH: True)
    (ORD: Ordinal.le i1 i0)
    (SIM: forall x_src, exists x_tgt, simg _ RR i1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR i0 (trigger (Take X_src) >>= ktr_src0) (trigger (Take X_tgt) >>= ktr_tgt0)
| simg_takeL
    i1 X ktr_src0 itr_tgt0
    (TAKEL: True)
    (ORD: Ordinal.lt i1 i0)
    (SIM: forall x, simg _ RR i1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR i0 (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_takeR
    i1 X itr_src0 ktr_tgt0
    (TAKER: True)
    (ORD: Ordinal.lt i1 i0)
    (SIM: exists x, simg _ RR i1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR i0 (itr_src0) (trigger (Take X) >>= ktr_tgt0)



(* | simg_stutter *)
(*     i1 itr_src itr_tgt *)
(*     (ORD: Ordinal.lt i1 i0) *)
(*     (SIM: simg _ RR i1 itr_src itr_tgt) *)
(*   : *)
(*     _simg simg RR i0 itr_src itr_tgt *)
.

Definition simg: forall R (RR: R -> R -> Prop), Ordinal.t -> (itree eventE R) -> (itree eventE R) -> Prop := paco5 _simg bot5.

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
(*   destruct (classic (Ordinal.lt o0 o1)). *)
(*   - pfold. econs; eauto. *)
(*   - *)
(* Qed. *)

Lemma simg_mon_ord r S SS i0 i1 (ORD: Ordinal.le i0 i1): @_simg r S SS i0 <2= @_simg r S SS i1.
Proof.
  ii. inv PR; try (by econs; et).
  - econs; try apply SIM; et. etrans; et.
  - econs; try apply SIM; et. eapply Ordinal.lt_le_lt; et.
  - econs; try apply SIM; et. eapply Ordinal.lt_le_lt; et.
  - econs; try apply SIM; et. etrans; et.
  - econs; try apply SIM; et. eapply Ordinal.lt_le_lt; et.
  - econs; try apply SIM; et. eapply Ordinal.lt_le_lt; et.
  - econs; try apply SIM; et. etrans; et.
  - econs; try apply SIM; et. eapply Ordinal.lt_le_lt; et.
  - econs; try apply SIM; et. eapply Ordinal.lt_le_lt; et.
Qed.

(* Lemma simg_mon_rel r S SS SS' (LE: SS <2= SS') i0: @_simg r S SS i0 <2= @_simg r S SS' i0. *)
(* Proof. *)
(*   ii. inv PR; try (by econs; et). *)
(*   - econs; et. ii. hexploit (SIM _ _ H); et. i. eapply LE. ii. econs; try apply SIM. etrans; et. *)
(*   - econs; try apply SIM. eapply Ordinal.lt_le_lt; et. *)
(*   - econs; try apply SIM. eapply Ordinal.lt_le_lt; et. *)
(*   - econs; try apply SIM. etrans; et. *)
(*   - econs; try apply SIM. eapply Ordinal.lt_le_lt; et. *)
(*   - econs; try apply SIM. eapply Ordinal.lt_le_lt; et. *)
(*   - econs; try apply SIM. etrans; et. *)
(*   - econs; try apply SIM. eapply Ordinal.lt_le_lt; et. *)
(*   - econs; try apply SIM. eapply Ordinal.lt_le_lt; et. *)
(*   - econs; try apply SIM. eapply Ordinal.lt_le_lt; et. *)
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






















Variant ordC (r: forall S (SS: S -> S -> Prop), Ordinal.t -> (itree eventE S) -> (itree eventE S) -> Prop):
  forall S (SS: S -> S -> Prop), Ordinal.t -> (itree eventE S) -> (itree eventE S) -> Prop :=
| ordC_intro
    o0 o1 R (RR: R -> R -> Prop) itr_src itr_tgt
    (ORD: Ordinal.le o0 o1)
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
(*   - econs; eauto. { eapply Ordinal.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. { eapply Ordinal.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. ii. spc SIM1. des. esplits; et. *)
(*   - econs; eauto. { eapply Ordinal.lt_le_lt; et. } des. esplits; et. econs; et. refl. *)
(*   - econs; eauto. { eapply Ordinal.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. ii. spc SIM1. des. esplits; et. *)
(*   - econs; eauto. { eapply Ordinal.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. { eapply Ordinal.lt_le_lt; et. } des. esplits; et. econs; et. refl. *)
(*   - econs. { eapply Ordinal.lt_le_lt; et. } econs; et. refl. *)
(* Qed. *)

(* Lemma ordC_compatible: compatible5 (_simg) ordC. *)
(* Proof. *)
(*   econs; eauto with paco. *)
(*   ii. inv PR. csc. *)
(*   rename x2 into o1. inv SIM. *)
(*   - econs; eauto. *)
(*   - econs; eauto. ii. econs; try apply SIM0; et. refl. *)
(*   - econs; eauto. econs; eauto with paco. *)
(*   - econs; eauto. { eapply Ordinal.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. { eapply Ordinal.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. ii. spc SIM0. des. esplits; et. *)
(*   - econs; eauto. { eapply Ordinal.lt_le_lt; et. } des. esplits; et. econs; et. refl. *)
(*   - econs; eauto. { eapply Ordinal.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. ii. spc SIM0. des. esplits; et. *)
(*   - econs; eauto. { eapply Ordinal.lt_le_lt; et. } econs; et. refl. *)
(*   - econs; eauto. { eapply Ordinal.lt_le_lt; et. } des. esplits; et. econs; et. refl. *)
(* Qed. *)

Lemma ordC_prespectful: prespectful5 (_simg) ordC.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  rename x2 into o1. apply GF in SIM. pfold. inv SIM.
  - econs; eauto.
  - econs; eauto. ii. right. left. eapply SIM0; et.
  - econs; eauto.
  - econs; eauto. { eapply Ordinal.lt_le_lt; et. }
  - econs; eauto. { eapply Ordinal.lt_le_lt; et. }
  - econs; eauto. ii. spc SIM0. des. esplits; et.
  - econs; eauto. { eapply Ordinal.lt_le_lt; et. } des. esplits; et.
  - econs; eauto. { eapply Ordinal.lt_le_lt; et. }
  - econs; eauto. ii. spc SIM0. des. esplits; et.
  - econs; eauto. { eapply Ordinal.lt_le_lt; et. }
  - econs; eauto. { eapply Ordinal.lt_le_lt; et. } des. esplits; et.
  (* - econs. { eapply Ordinal.lt_le_lt; et. } right. left. et. *)
Qed.

Lemma ordC_spec: ordC <6= gupaco5 (_simg) (cpn5 _simg).
Proof. intros. eapply prespect5_uclo; eauto with paco. eapply ordC_prespectful. Qed.
(* Lemma ordC_spec2: ordC <6= gupaco5 (_simg) (cpn5 _simg). *)
(* Proof. intros. gclo. econs. { apply ordC_compatible. } eapply ordC_mon; try apply PR. ii. gbase. ss. Qed. *)










Variant bindR (r s: forall S (SS: S -> S -> Prop), Ordinal.t -> (itree eventE S) -> (itree eventE S) -> Prop):
  forall S (SS: S -> S -> Prop), Ordinal.t -> (itree eventE S) -> (itree eventE S) -> Prop :=
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
    bindR r s SS (Ordinal.add o1 o0) (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
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
(* Hint Resolve Ordinal.lt_le_lt: ord. *)
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
    { instantiate (1:=o1). eapply Ordinal.add_base_l. }
    eapply simg_mon; eauto with paco.
  + rewrite ! bind_bind. econs; eauto. ii.
    { econs 2; eauto with paco. econs; eauto with paco. }


  + irw. econs; eauto.
    { eapply Ordinal.add_le_r; et. }
    { econs 2; eauto with paco. econs; eauto with paco. }
  + rewrite ! bind_tau. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    econs 2; eauto with paco. econs; eauto with paco.
  + irw. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    econs 2; eauto with paco. econs; eauto with paco.


  + rewrite ! bind_bind. econs; eauto.
    { eapply Ordinal.add_le_r; et. }
    { ii. spc SIM0. des. esplits; et. econs 2; eauto with paco. econs; eauto with paco. }
  + rewrite ! bind_bind. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.
  + rewrite ! bind_bind. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.

  + rewrite ! bind_bind. econs; eauto.
    { eapply Ordinal.add_le_r; et. }
    { ii. spc SIM0. des. esplits; et. econs 2; eauto with paco. econs; eauto with paco. }
  + rewrite ! bind_bind. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.
  + rewrite ! bind_bind. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
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
    simg SS (Ordinal.add o1 o0) (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt)
.
Proof.
  ginit.
  { eapply cpn5_wcompat; eauto with paco. }
  guclo bindC_spec. econs.
  - eauto with paco.
  - ii. exploit SIMK; eauto with paco.
Qed.




Definition eutt R (RR: R -> R -> Prop) (i0 i1: itree eventE R): Prop := exists o0, simg RR o0 i0 i1.

Require Import Coq.Logic.IndefiniteDescription.
Require Import ClassicalChoice ChoiceFacts.

Theorem eutt_bind
        R S (RR: R -> R -> Prop) (SS: S -> S -> Prop)
        i0 i1 k0 k1
        (LEFT: eutt RR i0 i1)
        (RIGHT: forall r0 r1 (SIM: RR r0 r1), eutt SS (k0 r0) (k1 r1))
  :
    eutt SS (i0 >>= k0) (i1 >>= k1)
.
Proof.
  r in LEFT. des.
  exploit (@choice { r0r1 : (R * R) | RR (fst r0r1) (snd r0r1) } Ordinal.t
                   (fun r0r1 o0 => simg SS o0 (k0 (fst (r0r1 $))) (k1 (snd (r0r1 $))))).
  { ii. destruct x. ss. destruct x; ss. exploit RIGHT; et. }
  i; des. clear RIGHT. rename x0 into RIGHT.
  r. unshelve eexists (Ordinal.add (Ordinal.join f) o0).
  eapply simg_bind; eauto. ii.
  unshelve exploit RIGHT; eauto. { eexists (_, _). ss. eauto. } intro A; ss.
  ginit.
  { eapply cpn5_wcompat. pmonauto. }
  guclo ordC_spec. econs.
  {
    unshelve eapply Ordinal.join_upperbound. eexists (_, _). ss. eauto.
  }
  gfinal. right.  ss.
Qed.





Definition myadd (o0 o1: Ordinal.t): Ordinal.t := Ordinal.mult (Ordinal.S o0) (Ordinal.S o1).

Lemma myadd_proj1 o0 o1: Ordinal.le o0 (myadd o0 o1).
Proof.
  unfold myadd. etransitivity.
  2: { eapply Ordinal.mult_S. }
  transitivity (Ordinal.S o0).
  { eapply Ordinal.lt_le. eapply Ordinal.S_lt. }
  { eapply Ordinal.add_base_r. }
Qed.

Lemma myadd_proj2 o0 o1: Ordinal.le o1 (myadd o0 o1).
Proof.
  unfold myadd. etransitivity.
  { eapply Ordinal.mult_1_l. }
  transitivity (Ordinal.mult (Ordinal.from_nat 1) (Ordinal.S o1)).
  { apply Ordinal.mult_le_r. apply Ordinal.lt_le. apply Ordinal.S_lt. }
  { apply Ordinal.mult_le_l. ss. erewrite <- Ordinal.S_le_mon. eapply Ordinal.O_bot. }
Qed.

Lemma myadd_le_l o0 o1 o2 (LE: Ordinal.le o0 o1): Ordinal.le (myadd o0 o2) (myadd o1 o2).
Proof.
  eapply Ordinal.mult_le_l. erewrite <- Ordinal.S_le_mon. auto.
Qed.

Lemma myadd_le_r o0 o1 o2 (LE: Ordinal.le o1 o2): Ordinal.le (myadd o0 o1) (myadd o0 o2).
Proof.
  eapply Ordinal.mult_le_r. erewrite <- Ordinal.S_le_mon. auto.
Qed.

Lemma myadd_lt_r o0 o1 o2 (LT: Ordinal.lt o1 o2): Ordinal.lt (myadd o0 o1) (myadd o0 o2).
Proof.
  eapply (@Ordinal.lt_le_lt (myadd o0 (Ordinal.S o1))).
  { unfold myadd. eapply Ordinal.lt_eq_lt.
    { eapply Ordinal.mult_S. }
    eapply Ordinal.lt_eq_lt.
    { eapply Ordinal.add_S. }
    eapply Ordinal.le_lt_lt.
    2: { eapply Ordinal.S_lt. }
    eapply Ordinal.add_base_l.
  }
  { eapply myadd_le_r. eapply Ordinal.S_spec in LT. auto. }
Qed.

Lemma myadd_lt_l o0 o1 o2 (LT: Ordinal.lt o0 o1): Ordinal.lt (myadd o0 o2) (myadd o1 o2).
Proof.
  unfold myadd. eapply Ordinal.lt_eq_lt.
  { eapply Ordinal.mult_S. }
  eapply Ordinal.eq_lt_lt.
  { eapply Ordinal.mult_S. }
  eapply Ordinal.le_lt_lt.
  2: { eapply Ordinal.add_lt_r. erewrite <- Ordinal.S_lt_mon. eapply LT. }
  eapply Ordinal.add_le_l.
  eapply Ordinal.mult_le_l.
  erewrite <- Ordinal.S_le_mon. eapply Ordinal.lt_le. auto.
Qed.

Hint Resolve myadd_proj1 myadd_proj2 myadd_le_l myadd_le_r myadd_lt_l myadd_lt_r: ord_proj.

Lemma ordinal_ind2
      (P: Ordinal.t -> Prop)
      (IH: forall o0 (IH: forall o1, Ordinal.lt o1 o0 -> P o1), P o0)
  :
    forall o0, P o0
.
Proof.
  revert IH. eapply well_founded_induction. { eapply Ordinal.lt_well_founded. }
Qed.

Lemma simg_inv_tauL
      R (RR: relation R)
      o0 i0 i1
      (SIM: simg RR o0 (tau;; i0) i1)
  :
    <<SIM: simg RR (Ordinal.S o0) i0 i1>>
.
Proof.
  move o0 at top. revert_until RR. pattern o0. eapply ordinal_ind2. clear o0.
  ii. punfold SIM. inv SIM; try by (irw in H0; csc).
  - pclearbot. ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. econs; cycle 1.
    { gstep. econs; eauto with paco. apply Ordinal.S_lt. }
    rewrite <- Ordinal.S_le_mon; et.
  - pclearbot. ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. econs; eauto with paco.
    etrans; eapply Ordinal.lt_le; et. eapply Ordinal.S_lt.
  - pclearbot. pfold. econs; eauto; cycle 1.
    { left. eapply IH; et. }
    rewrite <- Ordinal.S_lt_mon; et.
  - pclearbot. ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. econs; cycle 1.
    { gstep. econs; ss; cycle 1.
      { i. spc SIM0. gfinal; right. eapply IH; et. }
      rewrite <- Ordinal.S_lt_mon; et.
    }
    rewrite <- Ordinal.S_le_mon; et. refl.
  - des. pclearbot. exploit IH; et. intro A. pfold. econs; eauto with ord.
    rewrite <- Ordinal.S_lt_mon; et.
Qed.

Lemma simg_inv_tauR
      R (RR: relation R)
      o0 i0 i1
      (SIM: simg RR o0 i0 (tau;; i1))
  :
    <<SIM: simg RR (Ordinal.S o0) i0 i1>>
.
Proof.
  move o0 at top. revert_until RR. pattern o0. eapply ordinal_ind2. clear o0.
  ii. punfold SIM. inv SIM; try by (irw in H1; csc).
  - pclearbot. ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. econs; cycle 1.
    { gstep. econs; eauto with paco. apply Ordinal.S_lt. }
    rewrite <- Ordinal.S_le_mon; et.
  - pclearbot. pfold. econs; eauto; cycle 1.
    { left. eapply IH; et. }
    rewrite <- Ordinal.S_lt_mon; et.
  - pclearbot. ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. econs; eauto with paco.
    etrans; eapply Ordinal.lt_le; et. eapply Ordinal.S_lt.
  - des. pclearbot. exploit IH; et. intro A. pfold. econs; eauto with ord.
    rewrite <- Ordinal.S_lt_mon; et.
  - pclearbot. ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. econs; cycle 1.
    { gstep. econs; ss; cycle 1.
      { i. spc SIM0. gfinal; right. eapply IH; et. }
      rewrite <- Ordinal.S_lt_mon; et.
    }
    rewrite <- Ordinal.S_le_mon; et. refl.
Qed.

(* Lemma simg_inv_chooseL *)
(*       R (RR: relation R) *)
(*       X o0 k0 i1 *)
(*       (SIM: simg RR o0 (trigger (Choose X) >>= k0) i1) *)
(*   : *)
(*     exists x, <<SIM: simg RR (Ordinal.S o0) (k0 x) i1>> *)
(* . *)
(* Proof. *)
(*   move o0 at top. revert_until RR. pattern o0. eapply ordinal_ind2. clear o0. *)
(*   ii. punfold SIM. inv SIM; try by (irw in H0; csc). *)
(*   - pclearbot. exploit IH; et. intro A; des. *)
(*     esplits. pfold. econs; eauto. rewrite <- Ordinal.S_lt_mon; et. *)
(*   - irw in H0. csc. assert(ktr_src0 = k0) by ss. subst; clear_tac. *)
(*     esplits. pfold. econs; eauto. *)
(*     { eapply Ordinal.le_lt_lt; et. apply Ordinal.S_lt. } *)
(*     i. spc SIM0. des. pclearbot. left. instantiate (1:=x_src). et. ss. eapply IH; et. *)
(*   - des. pclearbot. pfold. econs; eauto; cycle 1. *)
(*     { esplits; et. left. eapply IH; et. } *)
(*     rewrite <- Ordinal.S_lt_mon; et. *)
(*   - irw in H1. csc. assert(ktr_tgt0  = k1) by ss. subst; clear_tac. *)
(*     spc SIM0. pclearbot. *)
(*     ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. econs; eauto with paco. *)
(*     etrans; eapply Ordinal.lt_le; et. eapply Ordinal.S_lt. *)
(*   - pfold. econs; eauto; cycle 1. *)
(*     { i. spc SIM0. pclearbot. left. eapply IH; et. } *)
(*     rewrite <- Ordinal.S_lt_mon; et. *)
(* Qed. *)

Lemma simg_inv_chooseR
      R (RR: relation R)
      X o0 i0 k1
      (SIM: simg RR o0 i0 (trigger (Choose X) >>= k1))
  :
    forall x, <<SIM: simg RR (Ordinal.S o0) i0 (k1 x)>>
.
Proof.
  move o0 at top. revert_until RR. pattern o0. eapply ordinal_ind2. clear o0.
  ii. punfold SIM. inv SIM; try by (irw in H1; csc).
  - pclearbot. exploit IH; et. intro A; des.
    pfold. econs; eauto. rewrite <- Ordinal.S_lt_mon; et.
  - irw in H1. csc. assert(ktr_tgt0  = k1) by ss. subst; clear_tac.
    pfold. econs; eauto. eapply Ordinal.le_lt_lt; et. apply Ordinal.S_lt.
  - des. pclearbot. pfold. econs; eauto; cycle 1.
    { esplits; et. left. eapply IH; et. }
    rewrite <- Ordinal.S_lt_mon; et.
  - irw in H1. csc. assert(ktr_tgt0  = k1) by ss. subst; clear_tac.
    spc SIM0. pclearbot.
    ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. econs; eauto with paco.
    etrans; eapply Ordinal.lt_le; et. eapply Ordinal.S_lt.
  - pfold. econs; eauto; cycle 1.
    { i. spc SIM0. pclearbot. left. eapply IH; et. }
    rewrite <- Ordinal.S_lt_mon; et.
Qed.



Lemma exists_forall_commute A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (exists (a: A), forall (b: B a), P a b) ->
    (forall (f: forall (a: A), B a), exists (a: A), P a (f a)).
Proof.
  i. des. esplits; eauto.
Qed.

Lemma exists_forall_commute_rev A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (forall (f: forall (a: A), B a), exists (a: A), P a (f a)) ->
    (exists (a: A), forall (b: B a), P a b).
Proof.
  i. eapply NNPP. ii. generalize (not_ex_all_not _ _ H0). i. clear H0.
  exploit non_dep_dep_functional_choice.
  { ii. eapply choice. auto. }
  { instantiate (1:=(fun a b => ~ P a b)).
    i. specialize (H1 x). eapply not_all_ex_not in H1; eauto. }
  i. des. specialize (H f). des. eapply x0; eauto.
Qed.

Lemma forall_exists_commute A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (forall (a: A), exists (b: B a), P a b)
    ->
    (exists (f: forall (a: A), B a), forall (a: A), P a (f a)).
Proof.
  i. eapply non_dep_dep_functional_choice; auto.
  ii. eapply choice. auto.
Qed.

Lemma forall_exists_commute_rev A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (exists (f: forall (a: A), B a), forall (a: A), P a (f a)) ->
    (forall (a: A), exists (b: B a), P a b).
Proof.
  i. des. eauto.
Qed.



Lemma simg_inv_takeR
      R (RR: relation R)
      X o0 i0 k1
      (SIM: simg RR o0 i0 (trigger (Take X) >>= k1))
  :
    exists x, <<SIM: simg RR (Ordinal.S o0) i0 (k1 x)>>
.
Proof.
  move o0 at top. revert_until RR. pattern o0. eapply ordinal_ind2. clear o0.
  ii. punfold SIM. inv SIM; try by (irw in H1; csc).
  - pclearbot. exploit IH; et. intro A; des.
    esplits. pfold. econs; eauto. rewrite <- Ordinal.S_lt_mon; et.
  - des. pclearbot. exploit IH; et. i; des. esplits; et. pfold. econs; eauto; cycle 1.
    rewrite <- Ordinal.S_lt_mon; et.
  - irw in H1. csc. assert(ktr_tgt0  = k1) by ss. subst; clear_tac.
    admit "????????".
  - admit "????????".
  - irw in H1. csc. assert(ktr_tgt0  = k1) by ss. subst; clear_tac.
    des. pclearbot.
    esplits; et.
    ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. econs; eauto with paco.
    etrans; et.
    { apply Ordinal.lt_le; et. }
    { eapply Ordinal.S_le. }
Qed.

(* Lemma simg_inv_chooseR2 *)
(*       R (RR: relation R) *)
(*       X0 X1 o0 k0 k1 *)
(*       (SIM: simg RR o0 (trigger (Choose X0) >>= k0) (trigger (Choose X1) >>= k1)) *)
(*   : *)
(*     forall x1, exists x0, <<SIM: simg RR o0 (k0 x0) (k1 x1)>> *)
(* . *)
(* Proof. *)
(*   (* destruct (classic (inhabited X1)); cycle 1. *) *)
(*   (* { ii. contradict H. econs; ss. } *) *)
(*   (* rename H into A. *) *)
(*   move o0 at top. revert_until RR. pattern o0. eapply ordinal_ind2; clear o0. *)
(*   ii. punfold SIM. inv SIM; (irw in H; irw in H0; irw in H1; csc). *)
(*   - assert(ktr_src0 = k0) by ss; assert(ktr_tgt0 = k1) by ss; subst; clear_tac. *)
(*     spc SIM0. des. pclearbot. esplits; eauto. *)
(*     ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. *)
(*   - assert(ktr_src0 = k0) by ss; subst; clear_tac. *)
(*     des. pclearbot. *)
(*     punfold SIM0. inv SIM0; irw in H; irw in H1; csc; pclearbot. *)
(*     + esplits; et. rewrite <- H0. eapply simg_inv_chooseR1; et. *)
(*       { intros ? ? A. irw in A. csc. } *)
(*       pfold. econs; ss; et. admit "ez". *)
(*     + assert(ktr_tgt0 = k1) by ss; subst; clear_tac. *)
(*       spc SIM. des. pclearbot. esplits; et. *)
(*       rewrite <- H0. pfold. econs; et. esplits; et. left. *)
(*       ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. *)
(*     + des. pclearbot. *)
(*       esplits; et. *)
(*       exploit IH; et. *)
(*       esplits; et. rewrite <- H0. pfold. econs; et. esplits; et. left. *)
(*       gfinal; right. rewrite <- H0. *)
(*       eauto with paco. *)
(*       rewrite <- H0. pfold. econs; et. esplits; et. left. *)
(*       esplits; et. rewrite <- H0. eapply simg_inv_chooseR1; et. *)
(*       { intros ? ? A. irw in A. csc. } *)
(*       pfold. econs; ss; et. admit "ez". *)
(*       ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. econs; ss. admit "". *)
(*       gfinal. right. *)
(*       ss. *)

(*     destruct (classic (forall X0 k0', (k0 x) <> trigger (Choose X0) >>= k0')). *)
(*     + eapply simg_inv_chooseR1 in H; et. pfold. econs; et. *)
(*       { apply Ordinal.S_lt. } *)
(*       i. left. exploit IH; et. *)
(*     punfold SIM0. inv SIM0; irw in H; csc; pclearbot. *)
(*     + *)
(*     exploit IH. et. esplits; eauto. *)
(*     ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. *)
(*   - *)
(*     eapply IH. et. *)
(*     esplits; eauto. *)
(*     pclearbot. exploit IH; et. intro A; des. *)
(*     pfold. econs; eauto. rewrite <- Ordinal.S_lt_mon; et. *)
(*   - irw in H1. csc. assert(ktr_tgt0  = k1) by ss. subst; clear_tac. *)
(*     pfold. econs; eauto. eapply Ordinal.le_lt_lt; et. apply Ordinal.S_lt. *)
(*   - des. pclearbot. pfold. econs; eauto; cycle 1. *)
(*     { esplits; et. left. eapply IH; et. } *)
(*     rewrite <- Ordinal.S_lt_mon; et. *)
(*   - irw in H1. csc. assert(ktr_tgt0  = k1) by ss. subst; clear_tac. *)
(*     spc SIM0. pclearbot. *)
(*     ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. econs; eauto with paco. *)
(*     etrans; eapply Ordinal.lt_le; et. eapply Ordinal.S_lt. *)
(*   - pfold. econs; eauto; cycle 1. *)
(*     { i. spc SIM0. pclearbot. left. eapply IH; et. } *)
(*     rewrite <- Ordinal.S_lt_mon; et. *)

(*   i. *)
(*   punfold *)
(* Qed. *)

(* Lemma simg_inv_chooseR1 *)
(*       R (RR: relation R) *)
(*       X o0 i0 k1 *)
(*       (NCHOOSE: forall X k0, i0 <> trigger (Choose X) >>= k0) *)
(*       (SIM: simg RR (Ordinal.S o0) i0 (trigger (Choose X) >>= k1)) *)
(*   : *)
(*     forall x, <<SIM: simg RR o0 i0 (k1 x)>> *)
(* . *)
(* Proof. *)
(*   move o0 at top. revert_until RR. pattern o0. eapply ClassicalOrdinal.ind; clear o0. *)
(*   { admit "". } *)
(*   { admit "". } *)
(*   ii. punfold SIM. inv SIM; try by (irw in H1; csc). *)
(*   - pclearbot. pfold. *)
(*     destruct (ClassicalOrdinal.limit_or_S o); des; cycle 1. *)
(*     + econs; et. { apply H. } left. *)
(*     + econs; et. { apply H. } left. *)
(*       punfold SIM0. inv SIM0; try by (irw in H2; csc). *)
(*       * eapply HELPER; ss. { apply H. }  { ii. irw in H0. clarify. } pclearbot. *)
(*         admit "ez". *)
(*       * *)
(*         eapply IH. *)
(*     + *)
(*     econs; et. *)
(*     ClassicalOrdinal *)
(*     eapply IH. *)
(*     exploit IH; cycle 1. *)
(*     { et. } *)
(*     exploit IH; cycle 1. *)
(*     { pfold. econs; ss. { apply Ordinal.S_lt. } et. } *)
(*     { intro A; des. admit "". } *)
(*     pfold. econs; eauto. rewrite <- Ordinal.S_lt_mon; et. *)
(*   - irw in H1. csc. assert(ktr_tgt0  = k1) by ss. subst; clear_tac. *)
(*     pfold. econs; eauto. eapply Ordinal.le_lt_lt; et. apply Ordinal.S_lt. *)
(*   - des. pclearbot. pfold. econs; eauto; cycle 1. *)
(*     { esplits; et. left. eapply IH; et. } *)
(*     rewrite <- Ordinal.S_lt_mon; et. *)
(*   - irw in H1. csc. assert(ktr_tgt0  = k1) by ss. subst; clear_tac. *)
(*     spc SIM0. pclearbot. *)
(*     ginit. { eapply cpn5_wcompat; pmonauto. } guclo ordC_spec. econs; eauto with paco. *)
(*     etrans; eapply Ordinal.lt_le; et. eapply Ordinal.S_lt. *)
(*   - pfold. econs; eauto; cycle 1. *)
(*     { i. spc SIM0. pclearbot. left. eapply IH; et. } *)
(*     rewrite <- Ordinal.S_lt_mon; et. *)
(* Qed. *)



Theorem simg_trans_gil
        R (RR: relation R) `{Transitive _ RR}
        o0 o1 o2 (i0 i1 i2: itree eventE R)
        (SIM0: simg RR o0 i0 i1)
        (SIM1: simg RR o1 i1 i2)
        (LE: Ordinal.le (myadd o0 o1) o2)
  :
    <<SIM: simg RR o2 i0 i2>>
.
Proof.
  revert_until H. pcofix CIH.
  eapply (ordinal_ind2 (fun o0 => forall o1 o2 i0 i1 i2 (SIM0: simg RR o0 i0 i1) (SIM1: simg RR o1 i1 i2) (LE: Ordinal.le (myadd o0 o1) o2), paco5 _simg r R RR o2 i0 i2)).
  i. punfold SIM1. inv SIM1.
  - (** ret **)
    clear IH. punfold SIM0. inv SIM0; try (by irw in H2; csc).
    { pfold. econs; eauto. }
    + pclearbot. pfold. econs; eauto.
      { instantiate (1:=i1). eapply (@Ordinal.lt_le_lt o0); auto.
        transitivity (myadd o0 o1); auto. eapply myadd_proj1. }
      punfold SIM1. left.
      revert SIM1. revert itr_src0. pattern i1. eapply ordinal_ind2. clears i1. clear i1. i.
      inv SIM1; try (by irw in H2; csc).
      * pfold. econs; eauto.
      * pclearbot. punfold SIM0. pfold. econs; eauto.
      * des. pfold. econs; eauto. pclearbot. esplits; eauto with paco.
        (* right. eapply CIH; et. instantiate (1:=Ordinal.O). admit "". *)
        left. eapply IH; et. punfold SIM0.
      * pfold. econs; eauto. i. spc SIM0. pclearbot.
        left. eapply IH; et. punfold SIM0.
    + des. pfold. econs; eauto.
      { instantiate (1:=(myadd i1 Ordinal.O)).
        eapply Ordinal.lt_le_lt; et.
        eapply Ordinal.lt_le_lt.
        - eapply myadd_lt_l; et.
        - eapply myadd_le_r. eapply Ordinal.O_is_O. }
      pclearbot. esplits; et.
      right. eapply CIH; et. refl.
    + pfold. econs; eauto.
      { instantiate (1:=(myadd i1 Ordinal.O)).
        eapply Ordinal.lt_le_lt; et.
        eapply Ordinal.lt_le_lt.
        - eapply myadd_lt_l; et.
        - eapply myadd_le_r. eapply Ordinal.O_is_O. }
      pclearbot. esplits; et.
      right. eapply CIH; et. refl.


  - (** syscall **)
    punfold SIM0. inv SIM0; try by (irw in H2; csc).
    + irw in H2; csc. assert(ktr_src0 = ktr_tgt1) by eauto; clarify. clear_tac.
      pfold. econs; eauto. ii. specialize (SIM x y H0). specialize (SIM1 x y H0). pclearbot. subst.
      right. eapply CIH; et. refl.
    + pclearbot. pfold. econs; eauto.
      { instantiate (1:=(myadd i1 Ordinal.O)).
        eapply Ordinal.lt_le_lt; et.
        eapply Ordinal.lt_le_lt.
        - eapply myadd_lt_l; et.
        - eapply myadd_le_r. eapply Ordinal.O_is_O. }
      left. eapply IH; et. refl.
    + des. pclearbot. pfold. econs; eauto.
      { instantiate (1:=(myadd i1 Ordinal.O)).
        eapply Ordinal.lt_le_lt; et.
        eapply Ordinal.lt_le_lt.
        - eapply myadd_lt_l; et.
        - eapply myadd_le_r. eapply Ordinal.O_is_O. }
      esplits; et. left. eapply IH; et. refl.
    + des. pclearbot. pfold. econs; eauto.
      { instantiate (1:=(myadd i1 Ordinal.O)).
        eapply Ordinal.lt_le_lt; et.
        eapply Ordinal.lt_le_lt.
        - eapply myadd_lt_l; et.
        - eapply myadd_le_r. eapply Ordinal.O_is_O. }
      esplits; et. left. eapply IH; et. refl.



  - (*** tau both ***)
    punfold SIM0. inv SIM0; try by (irw in H2; csc).
    { pfold. econs; ss; cycle 1.
      { pclearbot. right. eapply CIH; et. reflexivity. }
      etrans; et. etrans. { eapply myadd_le_l; et. } { eapply myadd_le_r; et. }
    }
    { pclearbot. eapply simg_inv_tauR in SIM1. des.
      pfold. econs; eauto. right. eapply CIH; eauto.
      transitivity (myadd (Ordinal.S i1) o1).
      { eapply myadd_le_r. auto. }
      { eapply myadd_le_l. eapply Ordinal.S_spec. auto. }
    }
    { pclearbot. pfold. econs; eauto; cycle 1.
      { right. eapply CIH; et. refl. }
      eapply Ordinal.lt_le_lt; et. eapply Ordinal.le_lt_lt.
      { instantiate (1:= myadd i1 o1). eapply myadd_le_r. auto. }
      { apply myadd_lt_l. auto. }
    }
    { des.  pclearbot. pfold. eapply simg_chooseL; ss; cycle 1.
      { esplits. right. eapply CIH; et. { pfold. econs; eauto. } refl. }
      eapply Ordinal.lt_le_lt; et. eapply Ordinal.le_lt_lt.
      { eapply myadd_le_r; eauto. refl. }
      { apply myadd_lt_l. auto. }
    }
    { pfold. eapply simg_takeL; ss; cycle 1.
      { esplits. spc SIM1. pclearbot. right. eapply CIH; et. { pfold. econs; eauto. } refl. }
      eapply Ordinal.lt_le_lt; et. eapply Ordinal.le_lt_lt.
      { eapply myadd_le_r; eauto. refl. }
      { apply myadd_lt_l. auto. }
    }



  - (** tauL **)
    punfold SIM0. inv SIM0; try by (irw in H2; csc).
    { pfold. econs; eauto.
      { instantiate (1:=myadd i1 i3).
        eapply (@Ordinal.lt_le_lt (myadd o0 o1)); auto.
        eapply (@Ordinal.lt_le_lt (myadd i1 o1)).
        { eapply myadd_lt_r. auto. }
        { eapply myadd_le_l. auto. }
      }
      pclearbot. right. eapply CIH; et. reflexivity.
    }
    { pclearbot. eapply simg_inv_tauR in SIM1. des.
      pfold. econs; eauto.
      { instantiate (1:=myadd (Ordinal.S i1) i3).
        eapply (@Ordinal.lt_le_lt (myadd o0 o1)); auto.
        eapply (@Ordinal.lt_le_lt (myadd (Ordinal.S i1) o1)); auto.
        { eapply myadd_lt_r. auto. }
        { eapply myadd_le_l. apply Ordinal.S_spec. auto. }
      }
      right. eapply CIH; eauto. reflexivity.
    }
    { pclearbot. eapply IH; eauto.
      transitivity (myadd o0 o1); auto. transitivity (myadd i1 o1).
      { eapply myadd_le_r. apply Ordinal.lt_le. auto. }
      { eapply myadd_le_l. apply Ordinal.lt_le. auto. }
    }
    { des. pclearbot. eapply simg_inv_tauR in SIM1. des.
      pfold. econs; eauto.
      { instantiate (1:=myadd (Ordinal.S i1) i3).
        eapply (@Ordinal.lt_le_lt (myadd o0 o1)); auto.
        eapply (@Ordinal.lt_le_lt (myadd (Ordinal.S i1) o1)); auto.
        { eapply myadd_lt_r. auto. }
        { eapply myadd_le_l. apply Ordinal.S_spec. auto. }
      }
      esplits. right. eapply CIH; eauto. reflexivity.
    }
    { pclearbot.
      pfold. econs; eauto.
      { instantiate (1:=myadd (Ordinal.S i1) i3).
        eapply (@Ordinal.lt_le_lt (myadd o0 o1)); auto.
        eapply (@Ordinal.lt_le_lt (myadd (Ordinal.S i1) o1)); auto.
        { eapply myadd_lt_r. auto. }
        { eapply myadd_le_l. apply Ordinal.S_spec. auto. }
      }
      i. eapply simg_inv_tauR in SIM1. des.
      right. eapply CIH; eauto. reflexivity.
    }


  - (** tauR **)
    pclearbot.
    pfold. econs; eauto.
    { instantiate (1:= myadd o0 i3). eapply (Ordinal.lt_le_lt); et. eapply myadd_lt_r; et. }
    right. eapply CIH; et. refl.


  - (** choose both **)
    punfold SIM0. inv SIM0; try by (irw in H2; csc).
    { pfold. econs; ss; cycle 1.
      { pclearbot. right. eapply CIH; et. reflexivity. }
      eapply Ordinal.lt_le_lt; et. eapply myadd_lt_l; et.
    }
    { irw in H2. csc. assert(ktr_src0 = ktr_tgt1) by ss; subst. clear_tac.
      pfold. econs; eauto. i. spc SIM. des. spc SIM1. des. pclearbot.
      esplits; et.
      right. eapply CIH; eauto.
      { etrans; et. { eapply myadd_le_l; et. } { eapply myadd_le_r; et. } }
    }
    { des. pclearbot. pfold. econs; eauto. i. spc SIM; des. pclearbot.
      eapply simg_inv_chooseR in SIM1.
      esplits; eauto.
      right. eapply CIH; et.
      etrans.
      { eapply myadd_le_l; et. eapply Ordinal.is_S_spec; et. apply Ordinal.S_is_S. }
      { eapply myadd_le_r; et. }
    }
    { irw in H2. csc. assert(ktr_src0 = ktr_tgt1) by ss; subst. clear_tac.
      pfold. econs; eauto; cycle 1.
      { i. spc SIM. des. spc SIM1. pclearbot. left. eapply IH; et. refl. }
      eapply Ordinal.lt_le_lt; et.
      eapply Ordinal.lt_le_lt; et.
      { eapply myadd_lt_l; et. }
      { eapply myadd_le_r; et. }
    }
    { rename o0 into ox. rename i1 into _ox. rename i3 into oy. rename o1 into oy'.
      pfold. eapply simg_takeL; et.
      { instantiate (1:=myadd _ox oy'). eapply Ordinal.lt_le_lt; et. apply myadd_lt_l; ss. }
      i. spc SIM1; des. pclearbot.
      { right. eapply CIH; et. refl. }
    }


  - (** chooseL **)
    des. pclearbot.
    punfold SIM0. inv SIM0; try by (irw in H2; csc).
    { pclearbot. eapply simg_inv_chooseR in SIM1. des.
      pfold. econs; et; cycle 1.
      { right. eapply CIH; eauto. reflexivity. }
      { eapply Ordinal.lt_le_lt; et.
        eapply Ordinal.le_lt_lt; et; cycle 1.
        { eapply myadd_lt_r; et. }
        { eapply myadd_le_l; et. eapply Ordinal.S_is_S; et. }
      }
    }
    { irw in H2. csc. assert(ktr_tgt0 = ktr_src0) by ss; subst; clear_tac.
      spc SIM1. des. pclearbot.
      pfold. econs; eauto; cycle 1.
      { esplits; et. right. eapply CIH; et. refl. }
      { eapply Ordinal.lt_le_lt; et.
        eapply Ordinal.le_lt_lt; et; cycle 1.
        { eapply myadd_lt_r; et. }
        { eapply myadd_le_l; et. }
      }
    }
    { des. pclearbot. eapply simg_inv_chooseR in SIM1. des.
      pfold. econs; et; cycle 1.
      { esplits; et. right. eapply CIH; eauto. reflexivity. }
      { eapply Ordinal.lt_le_lt; et.
        eapply Ordinal.le_lt_lt; et; cycle 1.
        { eapply myadd_lt_r; et. }
        { eapply myadd_le_l; et. eapply Ordinal.S_is_S; et. }
      }
    }
    { irw in H2. csc. assert(ktr_tgt0 = ktr_src0) by ss; subst; clear_tac.
      spc SIM1. des. pclearbot.
      eapply IH; et.
      { etrans; et.
        etrans.
        { eapply myadd_le_r; et. eapply Ordinal.lt_le; et. }
        { eapply myadd_le_l; et. eapply Ordinal.lt_le; et. }
      }
    }
    { pclearbot.
      pfold. econs; eauto; cycle 1.
      { i. eapply simg_inv_chooseR in SIM1. des.
        right. eapply CIH; eauto. reflexivity.
      }
      { eapply Ordinal.lt_le_lt; et.
        eapply Ordinal.le_lt_lt; et; cycle 1.
        { eapply myadd_lt_r; et. }
        { eapply myadd_le_l; et. eapply Ordinal.S_is_S; et. }
      }
    }

  - (** chooseR **)
    pclearbot.
    pfold. econs; eauto.
    { instantiate (1:= myadd o0 i3). eapply (Ordinal.lt_le_lt); et. eapply myadd_lt_r; et. }
    right. eapply CIH; et. refl.


  - (** take both **)
    punfold SIM0. inv SIM0; try by (irw in H2; csc).
    { pfold. econs; ss; cycle 1.
      { pclearbot. right. eapply CIH; et. reflexivity. }
      eapply Ordinal.lt_le_lt; et. eapply myadd_lt_l; et.
    }
    { des. pclearbot. pfold. econs; eauto.
      { instantiate (1:=myadd i1 o1).
        eapply Ordinal.lt_le_lt; et.
        eapply myadd_lt_l; et.
      }
      { esplits; et. right. eapply CIH; et. refl. }
    }
    { irw in H2. csc. assert(ktr_src0 = ktr_tgt1) by ss; subst. clear_tac.
      pfold. econs; eauto. i. spc SIM1. des. spc SIM. des. pclearbot.
      esplits; et.
      right. eapply CIH; eauto.
      { etrans; et. { eapply myadd_le_l; et. } { eapply myadd_le_r; et. } }
    }
    { rename o0 into ox. rename i1 into _ox. rename i3 into oy. rename o1 into oy'.
      pfold. eapply simg_takeL; et.
      { instantiate (1:=myadd _ox oy'). eapply Ordinal.lt_le_lt; et. apply myadd_lt_l; ss. }
      i. spc SIM1; des. pclearbot.
      { right. eapply CIH; et. refl. }
    }
    { irw in H2. csc. assert(ktr_src0 = ktr_tgt1) by ss; subst. clear_tac.
      des. pclearbot. spc SIM. des. pclearbot.
      pfold. econs; eauto; cycle 1.
      { esplits; et. left. eapply IH; et. refl. }
      eapply Ordinal.lt_le_lt; et.
      eapply Ordinal.lt_le_lt; et.
      { eapply myadd_lt_l; et. }
      { eapply myadd_le_r; et. }
    }



  - (** takeL **)
    des. pclearbot.
    punfold SIM0. inv SIM0; try by (irw in H2; csc).
    { pclearbot.
      pfold. econs; et; cycle 1.
      { right. eapply CIH; eauto. { pfold. econs; ss; [|eauto with paco]. et. } refl. }
      { eapply Ordinal.lt_le_lt; et.
        eapply myadd_lt_l; et.
      }
    }
    { des. pclearbot.
      pfold. econs; et; cycle 1.
      { esplits; et. right. eapply CIH; eauto.
        { pfold. econs; ss; [|eauto with paco]. et. }
        reflexivity. }
      { eapply Ordinal.lt_le_lt; et. eapply myadd_lt_l; et. }
    }
    { irw in H2. csc. assert(ktr_tgt0 = ktr_src0) by ss; subst; clear_tac.
      pfold. econs; et; cycle 1.
      { i. spc SIM1. des. spc SIM. pclearbot. right. eapply CIH; et. refl. }
      { eapply Ordinal.lt_le_lt; et.
        eapply Ordinal.le_lt_lt; et; cycle 1.
        { eapply myadd_lt_r; et. }
        { eapply myadd_le_l; et. }
      }
    }
    { pclearbot.
      pfold. econs; eauto; cycle 1.
      { i. right. eapply CIH; et.
        { pfold. econs; ss; [|eauto with paco]. et. }
        refl.
      }
      { eapply Ordinal.lt_le_lt; et.
        eapply myadd_lt_l; et.
      }
    }
    { irw in H2. csc. assert(ktr_tgt0 = ktr_src0) by ss; subst; clear_tac.
      des. spc SIM. pclearbot.
      eapply IH; et.
      { etrans; et.
        etrans.
        { eapply myadd_le_r; et. eapply Ordinal.lt_le; et. }
        { eapply myadd_le_l; et. eapply Ordinal.lt_le; et. }
      }
    }

  - (** takeR **)
    des. pclearbot.
    pfold. econs; eauto.
    { instantiate (1:= myadd o0 i3). eapply (Ordinal.lt_le_lt); et. eapply myadd_lt_r; et. }
    esplits; et. right. eapply CIH; et. refl.
Qed.










Variable md_src md_tgt: Mod.t.
Let ms_src: ModSem.t := md_src.(Mod.enclose).
Let ms_tgt: ModSem.t := md_tgt.(Mod.enclose).
(* Let sim_fnsem: relation (string * (list val -> itree Es val)) := *)
(*   fun '(fn_src, fsem_src) '(fn_tgt, fsem_tgt) => *)
(*     (<<NAME: fn_src = fn_tgt>>) /\ *)
(*     (<<SEM: forall varg, exists itr_src itr_tgt, *)
(*           (<<SRC: fsem_src varg = resum_itr itr_src>>) /\ *)
(*           (<<TGT: fsem_tgt varg = resum_itr itr_tgt>>) /\ *)
(*           (<<SIM: exists i0, simg i0 itr_src itr_tgt>>)>>) *)
(* . *)
(* Hypothesis (SIM: Forall2 sim_fnsem ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems)). *)

Hypothesis (SIM: exists o0, simg eq o0 (ModSem.initial_itr ms_src) (ModSem.initial_itr ms_tgt)).

Theorem adequacy_global: Beh.of_program (Mod.interp md_tgt) <1= Beh.of_program (Mod.interp md_src).
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
