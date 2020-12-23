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


Section SIM.

Context `{Σ: GRA.t}.

Section TY.
(* Context `{R: Type}. *)
Inductive _simg (simg: forall R, Ordinal.t -> relation (itree eventE R)) {R} (i0: Ordinal.t): relation (itree eventE R) :=
| simg_ret
    r
  :
    _simg simg i0 (Ret r) (Ret r)
| simg_syscall
    i1 ktr_src0 ktr_tgt0 fn m0 varg
    (SIM: (eq ==> simg _ i1)%signature ktr_src0 ktr_tgt0)
  :
    _simg simg i0 (trigger (Syscall fn m0 varg) >>= ktr_src0) (trigger (Syscall fn m0 varg) >>= ktr_tgt0)



| simg_tau
    i1 itr_src0 itr_tgt0
    (SIM: simg _ i1 itr_src0 itr_tgt0)
  :
    _simg simg i0 (tau;; itr_src0) (tau;; itr_tgt0)
| simg_tauL
    i1 itr_src0 itr_tgt0
    (ORD: Ordinal.lt i1 i0)
    (SIM: simg _ i1 itr_src0 itr_tgt0)
  :
    _simg simg i0 (tau;; itr_src0) (itr_tgt0)
| simg_tauR
    i1 itr_src0 itr_tgt0
    (ORD: Ordinal.lt i1 i0)
    (SIM: simg _ i1 itr_src0 itr_tgt0)
  :
    _simg simg i0 (itr_src0) (tau;; itr_tgt0)



| simg_choose
    i1 X_src X_tgt ktr_src0 ktr_tgt0
    (SIM: forall x_tgt, exists x_src, simg _ i1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg i0 (trigger (Choose X_src) >>= ktr_src0) (trigger (Choose X_tgt) >>= ktr_tgt0)
| simg_chooseL
    i1 X ktr_src0 itr_tgt0
    (ORD: Ordinal.lt i1 i0)
    (SIM: exists x, simg _ i1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg i0 (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_chooseR
    i1 X itr_src0 ktr_tgt0
    (ORD: Ordinal.lt i1 i0)
    (SIM: forall x, simg _ i1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg i0 (itr_src0) (trigger (Choose X) >>= ktr_tgt0)



| simg_take
    i1 X_src X_tgt ktr_src0 ktr_tgt0
    (SIM: forall x_src, exists x_tgt, simg _ i1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg i0 (trigger (Take X_src) >>= ktr_src0) (trigger (Take X_tgt) >>= ktr_tgt0)
| simg_takeL
    i1 X ktr_src0 itr_tgt0
    (ORD: Ordinal.lt i1 i0)
    (SIM: forall x, simg _ i1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg i0 (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_takeR
    i1 X itr_src0 ktr_tgt0
    (ORD: Ordinal.lt i1 i0)
    (SIM: exists x, simg _ i1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg i0 (itr_src0) (trigger (Take X) >>= ktr_tgt0)
.

Definition simg: forall R, Ordinal.t -> relation (itree eventE R) := paco4 _simg bot4.

Lemma simg_mon: monotone4 _simg.
Proof.
  ii. inv IN; try (by econs; et).
  - econs; et. ii. eapply LE; et.
  - econs; et. ii. hexploit SIM; et. i; des. esplits; et.
  - des. econs; et.
  - econs; et. ii. hexploit SIM; et. i; des. esplits; et.
  - des. econs; et.
Qed.
End TY.

Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.

Lemma simg_mon_ord r S i0 i1 (ORD: Ordinal.le i0 i1): @_simg r S i0 <2= @_simg r S i1.
Proof.
  ii. inv PR; try (by econs; et).
  - econs; ss; et. eapply Ordinal.lt_le_lt; et.
  - econs; ss; et. eapply Ordinal.lt_le_lt; et.
  - econs; ss; et. eapply Ordinal.lt_le_lt; et.
  - econs; ss; et. eapply Ordinal.lt_le_lt; et.
  - econs; ss; et. eapply Ordinal.lt_le_lt; et.
  - econs; ss; et. eapply Ordinal.lt_le_lt; et.
Qed.





Variant bindR (r s: forall S, Ordinal.t -> relation (itree eventE S)): forall S, Ordinal.t -> relation (itree eventE S) :=
| bindR_intro
    o0 o1

    R
    (i_src i_tgt: itree eventE R)
    (SIM: r _ o0 i_src i_tgt)

    S
    (k_src k_tgt: ktree eventE R S)
    (SIMK: forall (vret: R), s _ o1 (k_src vret) (k_tgt vret))
  :
    (* bindR r s (Ordinal.add o0 o1) (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt) *)
    bindR r s (Ordinal.add o1 o0) (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

Hint Constructors bindR: core.

Lemma bindR_mon
      r1 r2 s1 s2
      (LEr: r1 <4= r2) (LEs: s1 <4= s2)
  :
    bindR r1 s1 <4= bindR r2 s2
.
Proof. ii. destruct PR; econs; et. Qed.

Definition bindC r := bindR r r.
Hint Unfold bindC: core.

(* Hint Resolve Ordinal.add_base_r: ord. *)
(* Hint Resolve Ordinal.add_base_l: ord. *)
(* Hint Resolve Ordinal.lt_le_lt: ord. *)
(* Hint Resolve Ordinal.le_lt_lt: ord. *)

Lemma bindC_wrespectful: wrespectful4 (_simg) bindC.
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
    { econs 2; eauto with paco. econs; eauto with paco. }
  + rewrite ! bind_tau. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    econs 2; eauto with paco. econs; eauto with paco.
  + irw. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    econs 2; eauto with paco. econs; eauto with paco.


  + rewrite ! bind_bind. econs; eauto.
    { ii. spc SIM0. des. esplits; et. econs 2; eauto with paco. econs; eauto with paco. }
  + rewrite ! bind_bind. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.
  + rewrite ! bind_bind. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.

  + rewrite ! bind_bind. econs; eauto.
    { ii. spc SIM0. des. esplits; et. econs 2; eauto with paco. econs; eauto with paco. }
  + rewrite ! bind_bind. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.
  + rewrite ! bind_bind. econs; eauto.
    { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. }
    des. esplits; et. econs 2; eauto with paco. econs; eauto with paco.
Qed.

Lemma bindC_spec: bindC <5= gupaco4 (_simg) (cpn4 (_simg)).
Proof.
  intros. eapply wrespect4_uclo; eauto with paco. eapply bindC_wrespectful.
Qed.

Theorem simg_bind
        R S
        o0 (itr_src itr_tgt: itree eventE R)
        (SIM: simg o0 itr_src itr_tgt)
        o1 (ktr_src ktr_tgt: ktree eventE R S)
        (SIMK: forall varg, simg o1 (ktr_src varg) (ktr_tgt varg))
  :
    simg (Ordinal.add o1 o0) (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt)
.
Proof.
  ginit.
  { eapply cpn4_wcompat; eauto with paco. }
  guclo bindC_spec. econs.
  - eauto with paco.
  - ii. specialize (SIMK vret). eauto with paco.
Qed.









(* Variant transR (r s: forall S, Ordinal.t -> relation (itree eventE S)): forall S, Ordinal.t -> relation (itree eventE S) := *)
(* | transR_intro *)
(*     o0 o1 *)

(*     R *)
(*     (itr0 itr1 itr2: itree eventE R) *)
(*     (SIM0: r _ o0 itr0 itr1) *)
(*     (SIM1: s _ o1 itr1 itr2) *)
(*   : *)
(*     transR r s (Ordinal.add o1 o0) itr0 itr2 *)
(* . *)

(* Hint Constructors transR: core. *)

(* Lemma transR_mon *)
(*       r1 r2 s1 s2 *)
(*       (LEr: r1 <4= r2) (LEs: s1 <4= s2) *)
(*   : *)
(*     transR r1 s1 <4= transR r2 s2 *)
(* . *)
(* Proof. ii. destruct PR; econs; et. Qed. *)

(* Definition transC r := transR r r. *)
(* Hint Unfold transC: core. *)


(* Lemma transC_wrespectful: wrespectful4 (_simg) transC. *)
(* Proof. *)
(*   econstructor; repeat intro. *)
(*   { eapply transR_mon; eauto. } *)
(*   rename l into llll. *)
(*   eapply transR_mon in PR; cycle 1. *)
(*   { eapply GF. } *)
(*   { i. eapply PR0. } *)
(*   inv PR. csc. inv SIM0. *)
(*   + exploit GF; et. intro A. *)

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

Hypothesis (SIM: exists o0, simg o0 (ModSem.initial_itr ms_src) (ModSem.initial_itr ms_tgt)).

Theorem adequacy_global: Beh.of_program (Mod.interp md_tgt) <1= Beh.of_program (Mod.interp md_src).
Proof.
  admit "TODO".
Qed.

End SIM.
