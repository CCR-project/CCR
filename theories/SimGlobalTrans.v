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

Definition rel_compose R (RR0 RR1: R -> R -> Prop): R -> R -> Prop :=
  fun r0 r2 => exists r1, <<REL: RR0 r0 r1>> /\ <<REL: RR1 r1 r2>>.

Theorem simg_trans_gil
        R (RR0 RR1: R -> R -> Prop)
        o0 o1 o2 (i0 i1 i2: itree eventE R)
        (SIM0: simg RR0 o0 i0 i1)
        (SIM1: simg RR1 o1 i1 i2)
        (LE: Ordinal.le (myadd o0 o1) o2)
  :
    <<SIM: simg (rel_compose RR0 RR1) o2 i0 i2>>
.
Proof.
  revert_until RR1. pcofix CIH.
  eapply (ordinal_ind2 (fun o0 => forall o1 o2 i0 i1 i2 (SIM0: simg RR0 o0 i0 i1) (SIM1: simg RR1 o1 i1 i2) (LE: Ordinal.le (myadd o0 o1) o2), paco5 _simg r R (rel_compose RR0 RR1) o2 i0 i2)).
  i. punfold SIM1. inv SIM1.
  - (** ret **)
    clear IH. punfold SIM0. inv SIM0; try (by irw in H1; csc).
    { pfold. econs; eauto. r. esplits; et. }
    + pclearbot. pfold. econs; eauto.
      { instantiate (1:=i1). eapply (@Ordinal.lt_le_lt o0); auto.
        transitivity (myadd o0 o1); auto. eapply myadd_proj1. }
      punfold SIM1. left.
      revert SIM1. revert itr_src0. pattern i1. eapply ordinal_ind2. clears i1. clear i1. i.
      inv SIM1; try (by irw in H1; csc).
      * pfold. econs; eauto. r. esplits; et.
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
    punfold SIM0. inv SIM0; try by (irw in H1; csc).
    + irw in H1; csc. assert(ktr_src0 = ktr_tgt1) by eauto; clarify. clear_tac.
      pfold. econs; eauto. ii. specialize (SIM x y H). specialize (SIM1 x y H). pclearbot. subst.
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
    punfold SIM0. inv SIM0; try by (irw in H1; csc).
    { pfold. econs; ss; cycle 1.
      { pclearbot. right. eapply CIH; et. reflexivity. }
      etrans; et. etrans. { eapply myadd_le_l; et. } { eapply myadd_le_r; et. }
    }
    { rename o0 into ox. rename i1 into _ox. rename i3 into oy. rename o1 into oy'.
      pfold. eapply simg_tauL; et.
      { instantiate (1:=myadd _ox oy'). eapply Ordinal.lt_le_lt; et. apply myadd_lt_l; ss. }
      des. pclearbot.
      { right. eapply CIH; et. { pfold. econs; et. } refl. }
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
    punfold SIM0. inv SIM0; try by (irw in H1; csc).
    { pfold. econs; eauto.
      { instantiate (1:=myadd i1 i3).
        eapply (@Ordinal.lt_le_lt (myadd o0 o1)); auto.
        eapply (@Ordinal.lt_le_lt (myadd i1 o1)).
        { eapply myadd_lt_r. auto. }
        { eapply myadd_le_l. auto. }
      }
      pclearbot. right. eapply CIH; et. reflexivity.
    }
    { pfold. econs; et; cycle 1.
      { i. des. pclearbot. right. eapply CIH; et. { pfold. econs; ss; [|et]. et. } refl. }
      { eapply Ordinal.lt_le_lt; et.
        eapply myadd_lt_l; et.
      }
    }
    { pclearbot. eapply IH; eauto.
      transitivity (myadd o0 o1); auto. transitivity (myadd i1 o1).
      { eapply myadd_le_r. apply Ordinal.lt_le. auto. }
      { eapply myadd_le_l. apply Ordinal.lt_le. auto. }
    }
    { des. pclearbot.
      pfold. econs; et; cycle 1.
      { esplits; et. right. eapply CIH; eauto.
        { pfold. econs; ss; [|eauto with paco]. et. }
        reflexivity. }
      { eapply Ordinal.lt_le_lt; et. eapply myadd_lt_l; et. }
    }
    { pfold. econs; et; cycle 1.
      { i. spc SIM1. pclearbot. right. eapply CIH; et. { pfold. econs; ss; [|et]. et. } refl. }
      { eapply Ordinal.lt_le_lt; et.
        eapply myadd_lt_l; et.
      }
    }


  - (** tauR **)
    pclearbot.
    pfold. econs; eauto.
    { instantiate (1:= myadd o0 i3). eapply (Ordinal.lt_le_lt); et. eapply myadd_lt_r; et. }
    right. eapply CIH; et. refl.


  - (** choose both **)
    punfold SIM0. inv SIM0; try by (irw in H1; csc).
    { pfold. econs; ss; cycle 1.
      { pclearbot. right. eapply CIH; et. reflexivity. }
      eapply Ordinal.lt_le_lt; et. eapply myadd_lt_l; et.
    }
    { irw in H1. csc. assert(ktr_src0 = ktr_tgt1) by ss; subst. clear_tac.
      pfold. econs; eauto. i. spc SIM. des. spc SIM1. des. pclearbot.
      esplits; et.
      right. eapply CIH; eauto.
      { etrans; et. { eapply myadd_le_l; et. } { eapply myadd_le_r; et. } }
    }
    { rename o0 into ox. rename i1 into _ox. rename i3 into oy. rename o1 into oy'.
      pfold. eapply simg_chooseL; et.
      { instantiate (1:=myadd _ox oy'). eapply Ordinal.lt_le_lt; et. apply myadd_lt_l; ss. }
      des. pclearbot. esplits; et.
      { right. eapply CIH; et. refl. }
    }
    { irw in H1. csc. assert(ktr_src0 = ktr_tgt1) by ss; subst. clear_tac.
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
    punfold SIM0. inv SIM0; try by (irw in H1; csc).
    { pclearbot.
      pfold. econs; et; cycle 1.
      { right. eapply CIH; eauto. { pfold. econs; ss; [|et]. et. } reflexivity. }
      { eapply Ordinal.lt_le_lt; et.
        eapply myadd_lt_l; et.
      }
    }
    { irw in H1. csc. assert(ktr_tgt0 = ktr_src0) by ss; subst; clear_tac.
      spc SIM1. des. pclearbot.
      pfold. econs; eauto; cycle 1.
      { esplits; et. right. eapply CIH; et. refl. }
      { eapply Ordinal.lt_le_lt; et.
        eapply Ordinal.le_lt_lt; et; cycle 1.
        { eapply myadd_lt_r; et. }
        { eapply myadd_le_l; et. }
      }
    }
    { des. pclearbot.
      pfold. econs; et; cycle 1.
      { esplits; et. right. eapply CIH; eauto. { pfold. econs; ss; [|et]. et. } reflexivity. }
      { eapply Ordinal.lt_le_lt; et.
        eapply myadd_lt_l; et.
      }
    }
    { irw in H1. csc. assert(ktr_tgt0 = ktr_src0) by ss; subst; clear_tac.
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
      { i. spc SIM1. right. eapply CIH; eauto. { pfold. econs; ss; [|et]. et. } reflexivity. }
      { eapply Ordinal.lt_le_lt; et.
        eapply myadd_lt_l; et.
      }
    }

  - (** chooseR **)
    pclearbot.
    pfold. econs; eauto.
    { instantiate (1:= myadd o0 i3). eapply (Ordinal.lt_le_lt); et. eapply myadd_lt_r; et. }
    right. eapply CIH; et. refl.


  - (** take both **)
    punfold SIM0. inv SIM0; try by (irw in H1; csc).
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
    { irw in H1. csc. assert(ktr_src0 = ktr_tgt1) by ss; subst. clear_tac.
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
    { irw in H1. csc. assert(ktr_src0 = ktr_tgt1) by ss; subst. clear_tac.
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
    punfold SIM0. inv SIM0; try by (irw in H1; csc).
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
    { irw in H1. csc. assert(ktr_tgt0 = ktr_src0) by ss; subst; clear_tac.
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
    { irw in H1. csc. assert(ktr_tgt0 = ktr_src0) by ss; subst; clear_tac.
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

Theorem eutt_trans
        R (RR0: relation R) (RR1: relation R)
        (i0 i1 i2: itree eventE R)
        (SIM0: eutt RR0 i0 i1)
        (SIM1: eutt RR1 i1 i2)
  :
    <<SIM: eutt (rel_compose RR0 RR1) i0 i2>>
.
Proof. r in SIM0. r in SIM1. des. rr. esplits; et. eapply simg_trans_gil; et. refl. Qed.

Global Program Instance eutt_PreOrder R RR `{PreOrder R RR}: PreOrder (eutt RR).
Next Obligation.
  ii. rr. eexists Ordinal.O. refl.
Qed.
Next Obligation.
  ii.
  replace RR with (@rel_compose R RR RR); cycle 1.
  { unfold rel_compose. do 2 (apply func_ext; i). apply prop_ext. split; i; des; subst; et.
    { etrans; et. }
    esplits; et. refl.
  }
  eapply eutt_trans; et.
Qed.

(* Global Program Instance eutt_eq_PreOrder R: PreOrder (eutt (@eq R)). *)

Theorem tau_euttR
        R (RR: relation R) `{Reflexive _ RR}
        (i0: itree eventE R)
  :
    <<SIM: eutt RR i0 (tau;; i0)>>
.
Proof.
  rr. exists (Ordinal.S Ordinal.O). pfold. econs; et. { apply Ordinal.S_lt. } left.
  eapply simg_paco_refl; et.
Qed.

Theorem tau_euttL
        R (RR: relation R) `{Reflexive _ RR}
        (i0: itree eventE R)
  :
    <<SIM: eutt RR (tau;; i0) i0>>
.
Proof.
  rr. exists (Ordinal.S Ordinal.O). pfold. econs; et. { apply Ordinal.S_lt. } left.
  eapply simg_paco_refl; et.
Qed.


Fixpoint ntaus {E} (n: nat): itree E unit :=
  match n with
  | O => Ret tt
  | S n => tau;; (ntaus n)
  end
.

Require Import RelationClasses.

Goal eutt eq (Ret 1) (n <- trigger (Choose _);; ntaus n;; Ret 1).
Proof.
  replace (Ret 1) with ((Ret tt: itree eventE _) >>= (fun _ => Ret 1)) at 1; cycle 1.
  { irw; ss. }
  rewrite <- ! bind_bind.
  apply eutt_bind with (RR:=top2); cycle 1.
  { i. r. exists Ordinal.O. esplits; et. }
  replace (Ret tt) with ((Ret 42%nat: itree eventE _) >>= (fun _ => Ret tt)) at 1; cycle 1.
  { irw; ss. }
  apply eutt_bind with (RR:=top2).
  { replace (trigger (Choose nat)) with ((trigger (Choose nat)) >>= (fun n => Ret n)); cycle 1.
    { irw; ss. }
    r. exists (Ordinal.S Ordinal.O). pfold. econs; et. apply Ordinal.S_lt. }
  i. induction r1; ii; ss.
  { r. exists (Ordinal.S Ordinal.O). pfold. econs; et. }
  { etrans; et. r. exists (Ordinal.S Ordinal.O). pfold. econs; et. { apply Ordinal.S_lt. } left.
    eapply simg_paco_refl; ss. }
Qed.

Goal eutt eq (Ret 1) (n <- trigger (Choose _);; ntaus n;; m <- trigger (Choose _);; ntaus m;; Ret 1).
Proof.
  replace (Ret 1) with ((Ret 1: itree eventE _) >>= (fun x => Ret x)); cycle 1.
  { irw. ss. }
  apply eutt_bind with (RR:=fun n _ => n = 1).
  { r. exists (Ordinal.S Ordinal.O).
    replace (trigger (Choose nat)) with ((trigger (Choose nat)) >>= (fun n => Ret n)); cycle 1.
    { irw; ss. }
    pfold. econs; et. apply Ordinal.S_lt.
  }
  i. subst.
  replace (Ret 1) with ((Ret 1: itree eventE _) >>= (fun x => Ret x)); cycle 1.
  { irw. ss. }
  rewrite <- bind_bind.
  apply eutt_bind with (RR:=fun n _ => n = 1).
  {
    replace (Ret 1) with ((Ret tt: itree eventE _) >>= (fun _ => Ret 1)); cycle 1.
    { irw. ss. }
    eapply eutt_bind with (RR:=top2).
    { r. exists (Ordinal.from_nat r1).
      induction r1; ii; ss.
      - pfold. econs; et.
      - pfold. econs; et. apply Ordinal.S_lt.
    }
    i. r.
    exists (Ordinal.S Ordinal.O).
    replace (trigger (Choose nat)) with ((trigger (Choose nat)) >>= (fun n => Ret n)); cycle 1.
    { irw; ss. }
    pfold. econs; et. apply Ordinal.S_lt.
  }
  i. subst.
  replace (Ret 1) with ((Ret 1: itree eventE _) >>= (fun x => Ret x)); cycle 1.
  { irw. ss. }
  rewrite <- bind_bind.
  apply eutt_bind with (RR:=fun n m => n = 1 /\ m = 1).
  {
    replace (Ret 1) with ((Ret tt: itree eventE _) >>= (fun _ => Ret 1)); cycle 1.
    { irw. ss. }
    eapply eutt_bind with (RR:=top2).
    { r. exists (Ordinal.from_nat r2).
      induction r2; ii; ss.
      - pfold. econs; et.
      - pfold. econs; et. apply Ordinal.S_lt.
    }
    i. r.
    exists (Ordinal.S Ordinal.O). irw. pfold. econs; et.
  }
  i. des; subst.
  r. exists (Ordinal.S Ordinal.O). pfold. econs; et.
Qed.

Theorem cancel
      X R (RR: R -> R -> Prop) `{Reflexive _ RR}
      (code: X -> X -> itree eventE R)
  :
    eutt RR (n <- trigger (Choose X);; code n n)
         (n <- trigger (Choose X);; m <- trigger (Take X);; code n m).
Proof.
  r. exists (Ordinal.from_nat 5). pfold. econs; et.
  { refl. }
  i. esplits; et. left. pfold. econs; et. { ss. apply Ordinal.S_lt. } esplits; et. left.
  eapply simg_paco_refl; et.
Qed.

Theorem cancel_assume_guarantee
      (P: Prop) R (RR: R -> R -> Prop) `{Reflexive _ RR}
      (code: itree eventE R)
  :
    eutt RR code (guarantee P;; assume P;; code).
Proof.
  r. exists (Ordinal.from_nat 5). unfold assume, guarantee.
  repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r).
  pfold. econs; eauto. { ss. apply Ordinal.S_lt. }
  i. left. pfold. econs; eauto. { ss. apply Ordinal.S_lt. }
  esplits; et. left. eapply simg_paco_refl; et.
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