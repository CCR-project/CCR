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



Let eventE := void1.

Section SIM.

Context `{Σ: GRA.t}.

Section TY.
(* Context `{R: Type}. *)
Inductive _simg (simg: forall R (RR: relation R), Ordinal.t -> relation (itree eventE R))
          {R} (RR: relation R) (i0: Ordinal.t): relation (itree eventE R) :=
| simg_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg simg RR i0 (Ret r_src) (Ret r_tgt)
(* | simg_syscall *)
(*     i1 ktr_src0 ktr_tgt0 fn m0 varg *)
(*     (SIM: (eq ==> simg _ RR i1)%signature ktr_src0 ktr_tgt0) *)
(*   : *)
(*     _simg simg RR i0 (trigger (Syscall fn m0 varg) >>= ktr_src0) (trigger (Syscall fn m0 varg) >>= ktr_tgt0) *)



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



(* | simg_stutter *)
(*     i1 itr_src itr_tgt *)
(*     (ORD: Ordinal.lt i1 i0) *)
(*     (SIM: simg _ RR i1 itr_src itr_tgt) *)
(*   : *)
(*     _simg simg RR i0 itr_src itr_tgt *)
.

Definition simg: forall R (RR: relation R), Ordinal.t -> relation (itree eventE R) := paco5 _simg bot5.

Lemma simg_mon: monotone5 _simg.
Proof.
  ii. inv IN; try (by econs; et).
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
  (* - econs; try apply SIM. eapply Ordinal.lt_le_lt; et. *)
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






















Variant ordC (r: forall S (SS: relation S), Ordinal.t -> relation (itree eventE S)):
  forall S (SS: relation S), Ordinal.t -> relation (itree eventE S) :=
| ordC_intro
    o0 o1 R (RR: relation R) itr_src itr_tgt
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

Lemma ordC_compatible: compatible5 (_simg) ordC.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  rename x2 into o1. inv SIM.
  - econs; eauto.
  - econs; eauto.
  - econs; eauto. { eapply Ordinal.lt_le_lt; et. } econs; et. refl.
  - econs; eauto. { eapply Ordinal.lt_le_lt; et. } econs; et. refl.
Qed.

Lemma ordC_prespectful: prespectful5 (_simg) ordC.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  rename x2 into o1. apply GF in SIM. pfold. inv SIM.
  - econs; eauto.
  - econs; eauto.
  - econs; eauto. { eapply Ordinal.lt_le_lt; et. }
  - econs; eauto. { eapply Ordinal.lt_le_lt; et. }
  (* - econs. { eapply Ordinal.lt_le_lt; et. } right. left. et. *)
Qed.

Lemma ordC_spec: ordC <6= gupaco5 (_simg) (cpn5 _simg).
Proof. intros. eapply prespect5_uclo; eauto with paco. eapply ordC_prespectful. Qed.
Lemma ordC_spec2: ordC <6= gupaco5 (_simg) (cpn5 _simg).
Proof. intros. gclo. econs. { apply ordC_compatible. } eapply ordC_mon; try apply PR. ii. gbase. ss. Qed.











Variant bindR (r s: forall S (SS: relation S), Ordinal.t -> relation (itree eventE S)):
  forall S (SS: relation S), Ordinal.t -> relation (itree eventE S) :=
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


  + irw. econs; eauto.
    { eapply Ordinal.add_le_r; et. }
    { econs 2; eauto with paco. econs; eauto with paco. }
  + rewrite ! bind_tau. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    econs 2; eauto with paco. econs; eauto with paco.
  + irw. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    econs 2; eauto with paco. econs; eauto with paco.
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













Variant transR (r s: forall S (SS: relation S), Ordinal.t -> relation (itree eventE S)):
  forall S (SS: relation S), Ordinal.t -> relation (itree eventE S) :=
| transR_intro
    o0 o1

    S (SS: relation S)
    itr0 itr1 itr2
    (TRANS: Transitive SS)
    (SIM0: r _ SS o0 itr0 itr1)
    (SIM1: s _ SS o1 itr1 itr2)
  :
    transR r s SS (Ordinal.add o1 o0) itr0 itr2
.

Hint Constructors transR: core.

Lemma transR_mon
      r1 r2 s1 s2
      (LEr: r1 <5= r2) (LEs: s1 <5= s2)
  :
    transR r1 s1 <5= transR r2 s2
.
Proof. ii. destruct PR; econs; et. Qed.

Definition transC r := transR r r.
Hint Unfold transC: core.



Fixpoint ntaus (n: nat): itree eventE unit :=
  match n with
  | O => Ret tt
  | S n => tau;; (ntaus n)
  end
.

Definition my_eutt R (i0 i1: itree eventE R): Prop :=
  <<EUTT: exists n, (ntaus n);; i0 = i1>> \/ <<EUTT: exists n, i0 = (ntaus n);; i1>>
.


Lemma ind3
      (P: Ordinal.t -> Prop)
      (IH: forall o0 (IH: forall o1, Ordinal.lt o1 o0 -> P o1), P o0)
  :
    forall o0, P o0
.
Proof.
  revert IH. eapply well_founded_induction. { eapply Ordinal.lt_well_founded. }
Qed.

(* Lemma add_lt_r *)
(*       o0 o1 o2 *)
(*   : *)
(*     Ordinal.lt o1 o2 -> Ordinal.lt (Ordinal.add o1 o0) (Ordinal.add o2 o0) *)
(* . *)
(* Proof. *)
(*   admit "TODO". *)
(* Qed. *)



Theorem simg_trans
        R (RR: relation R) `{Transitive _ RR}
        o0 o1 o2 (i0 i1 i2 i3: itree eventE R)
        (SIM0: simg RR o0 i0 i1)
        (SIM1: simg RR o1 i2 i3)
        (EUTT: my_eutt i1 i2)
        (LE: Ordinal.le (Ordinal.add o0 o1) o2)
  :
    <<SIM: simg RR o2 i0 i2>>
.
Proof.
  revert_until H. pcofix CIH. i.
  move o2 at top. revert_until CIH. pattern o2. eapply ind3; i; clear o2.
  punfold SIM0. inv SIM0; pclearbot.
  - (*** ret ***)
    admit "TODO".
  - (*** tau ***)
    punfold SIM1. inv SIM1; pclearbot.
    + (*** ret ***)
      admit "TODO".
    + (*** tau ***)
      pfold. econs; eauto. right. eapply CIH; eauto.
      { admit "ez - myeutt". }
      { etrans. - eapply Ordinal.add_le_l; et. - eapply Ordinal.add_le_r; et. }
    + (*** tauL ***)
      pfold. econs; eauto. right. eapply CIH; eauto.
      { admit "ez - myeutt". }
      { etrans. - eapply Ordinal.add_le_l; et. - eapply Ordinal.add_le_r; et. eapply Ordinal.lt_le; et. }
    + (*** tauR ***)
      pfold. econs; eauto.
      { instantiate (1:=(Ordinal.add i4 i1)).
        eapply Ordinal.lt_le_lt; try apply LE.
        eapply Ordinal.lt_le_lt. - eapply Ordinal.add_lt_r; et. - eapply Ordinal.add_le_l; et. }
      (*** this inductive proof also works...
           left. eapply IH; et.
       ***)
      right. eapply CIH; et.
      { admit "ez- - myeutt". }
      refl.
  - (*** tauL ***)
    pfold. econs; eauto.
    { instantiate (1:=(Ordinal.add i4 o3)).
      eapply Ordinal.lt_le_lt; try apply LE.
      eapply Ordinal.lt_le_lt. - eapply Ordinal.add_lt_r; et. - eapply Ordinal.add_le_l; et. }
  - (*** tauR ***)
Qed.



Lemma transC_prespectful: prespectful5 (_simg) transC.
Proof.
  econstructor; repeat intro.
  { eapply transR_mon; eauto. }
  rename l into llll.
  rename r into rrrr.
  eapply transR_mon in PR; cycle 1.
  { eapply GF. }
  { i. eapply PR0. }
  inv PR. csc. rename x3 into itr_src. rename x4 into itr_tgt. rename itr1 into itr_mid. rename x0 into S. rename x1 into SS.
  apply GF in SIM1.
  revert_until SS. pcofix CIH. i.
  move o0 at top. revert_until SS. pattern o0. eapply ind2; i; clear o0.
  TTTTTTTTTTTTTTTTTT
  inv SIM0; try rename itr_tgt into r_mid.
  - move o0 at top. revert_until SS. pattern o0. eapply ind2; i; clear o0.
    + exploit IH; et. intro M. eapply simg_mon_ord; et. eapply Ordinal.add_le_r. eapply Ordinal.lt_le; try apply SUCC.
    + exploit IH; et. intro M. eapply simg_mon_ord; et. eapply Ordinal.add_le_r. apply JOIN.
  - move o0 at top. revert_until SS. pattern o0. eapply ind2; i; clear o0.
    + exploit IH; et. intro M. eapply simg_mon_ord; et. eapply Ordinal.add_le_r. eapply Ordinal.lt_le; try apply SUCC.
    + exploit IH; et. intro M. eapply simg_mon_ord; et. eapply Ordinal.add_le_r. apply JOIN.
  - move o0 at top. revert_until SS. pattern o0. eapply ind2; i; clear o0.
    + rename o1 into ox. rename o into o0. rename s into o1. rename i1 into o1'.
      econs; eauto.
      { eapply Ordinal.add_lt_r. eapply SUCC. }
      econs.
Abort.

Lemma transC_prespectful: prespectful5 (_simg) transC.
Proof.
  econstructor; repeat intro.
  { eapply transR_mon; eauto. }
  rename l into llll.
  eapply transR_mon in PR; cycle 1.
  { eapply GF. }
  { i. eapply PR0. }
  inv PR. csc.
  rename x3 into itr_src. rename x4 into itr_tgt. rename itr1 into itr_mid. rename x0 into S. rename x1 into SS.
  revert_until SS. pcofix CIH. rename r0 into uu. i. pfold.
  apply GF in SIM1.
  ides itr_src.
  - ides itr_tgt.
    + econs; eauto. admit "ez".
    + dependent destruction SIM1; ss; try (by irw in x; csc).
      * econs; eauto.
  (* apply GF in SIM1. *)
  move o0 at top. revert_until SS. pattern o0. eapply ind2; i; clear o0.
  - inv SIM0.
    + rename r_tgt into r_mid.
      exploit IH; et. intro M. eapply simg_mon_ord; et. eapply Ordinal.add_le_r. eapply Ordinal.lt_le; try apply SUCC.
    + exploit IH; et. intro M. eapply simg_mon_ord; et. eapply Ordinal.add_le_r. eapply Ordinal.lt_le; try apply SUCC.
    + exploit IH; et. intro M. eapply simg_mon_ord; et. eapply Ordinal.add_le_r. eapply Ordinal.lt_le; try apply SUCC.
  -
      pfold. econs; eauto.
    exploit IH; et. intro M. eapply simg_mon_ord; et. eapply Ordinal.add_le_r. eapply Ordinal.lt_le; try apply SUCC.


  inv SIM0; try rename itr_tgt into r_mid.
  - move o0 at top. revert_until SS. pattern o0. eapply ind2; i; clear o0.
    + exploit IH; et. intro M. eapply simg_mon_ord; et. eapply Ordinal.add_le_r. eapply Ordinal.lt_le; try apply SUCC.
    + exploit IH; et. intro M. eapply simg_mon_ord; et. eapply Ordinal.add_le_r. apply JOIN.
  - move o0 at top. revert_until SS. pattern o0. eapply ind2; i; clear o0.
    + exploit IH; et. intro M. eapply simg_mon_ord; et. eapply Ordinal.add_le_r. eapply Ordinal.lt_le; try apply SUCC.
    + exploit IH; et. intro M. eapply simg_mon_ord; et. eapply Ordinal.add_le_r. apply JOIN.
  - move o0 at top. revert_until SS. pattern o0. eapply ind2; i; clear o0.
    + rename o1 into ox. rename o into o0. rename s into o1. rename i1 into o1'.
      econs; eauto.
      { eapply Ordinal.add_lt_r. eapply SUCC. }
      econs.
Abort.
(* Theorem simg_trans *)
(*         R *)
(*         o0 o1 (itr0 itr1 itr2: itree eventE R) *)
(*         (SIM0: simg o0 itr0 itr1) *)
(*         (SIM1: simg o1 itr1 itr2) *)
(*   : *)
(*     simg (Ordinal.add o1 o0) itr0 itr2 *)
(* . *)
(* Proof. *)
(*   ginit. *)
(*   { eapply cpn4_wcompat; eauto with paco. } *)
(*   guclo bindC_spec. econs. *)
(*   - eauto with paco. *)
(*   - ii. specialize (SIMK vret). eauto with paco. *)
(* Qed. *)


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
