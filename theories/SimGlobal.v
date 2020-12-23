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

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.


Section SIM.

Context `{Σ: GRA.t}.

Variable idx: Type.
Variable ord: idx -> idx -> Prop.
Hypothesis wf_ord: well_founded ord.

Section TY.
(* Context `{R: Type}. *)
Inductive _simg (simg: forall R, idx -> relation (itree eventE R)) {R} (i0: idx): relation (itree eventE R) :=
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
    (ORD: ord i1 i0)
    (SIM: simg _ i1 itr_src0 itr_tgt0)
  :
    _simg simg i0 (tau;; itr_src0) (itr_tgt0)
| simg_tauR
    i1 itr_src0 itr_tgt0
    (ORD: ord i1 i0)
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
    (ORD: ord i1 i0)
    (SIM: exists x, simg _ i1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg i0 (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_chooseR
    i1 X itr_src0 ktr_tgt0
    (ORD: ord i1 i0)
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
    (ORD: ord i1 i0)
    (SIM: forall x, simg _ i1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg i0 (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_takeR
    i1 X itr_src0 ktr_tgt0
    (ORD: ord i1 i0)
    (SIM: exists x, simg _ i1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg i0 (itr_src0) (trigger (Take X) >>= ktr_tgt0)
.

Definition simg: forall R, idx -> relation (itree eventE R) := paco4 _simg bot4.

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



(*** TODO: for bind rule, take a look at "respectful" thing again. ***)
Variable add: idx -> idx -> idx.
Variant bindR (r s: forall S, idx -> relation (itree eventE S)): forall S, idx -> relation (itree eventE S) :=
| bindR_intro
    o0 o1

    R
    (i_src i_tgt: itree eventE R)
    (SIM: simg o0 i_src i_tgt)

    S
    (k_src k_tgt: ktree eventE R S)
    (SIMK: forall (vret: R), simg o1 (k_src vret) (k_tgt vret))
  :
    bindR r s (add o0 o1) (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
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

(* Lemma bindC_wrespectful: wrespectful4 (_sim_st lt) bindC. *)
(* Proof. *)
(*   econstructor; repeat intro. *)
(*   { eapply bindR_mon; eauto. } *)
(*   rename l into llll. *)
(*   eapply bindR_mon in PR; cycle 1. *)
(*   { eapply GF. } *)
(*   { i. eapply PR0. } *)
(*   inv PR. csc. inv SIM. *)
(*   + irw. *)
(*     exploit SIMK; eauto. i. *)
(*     eapply sim_st_mon_ord. *)
(*     { instantiate (1:=i1). rewrite rtc_lt. lia. } *)
(*     eapply sim_st_mon; eauto with paco. *)
(*   + irw. econs; eauto. *)
(*     { econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*   + irw. econs; eauto. *)
(*     { econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*   + irw. econs; eauto. *)
(*   + irw. econs; eauto. *)
(*   + irw. econs; eauto. *)
(*     { ii. spc SIM0. des. esplits; eauto. *)
(*       econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*   + irw. des. econs; eauto. *)
(*     { esplits; eauto. *)
(*       econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*     { rewrite tc_lt in *. lia. } *)
(*   + irw. econs; eauto. ii. spc SIM0. des. esplits; eauto. *)
(*     { econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*     { rewrite tc_lt in *. lia. } *)
(*   + irw. econs; eauto. *)
(*     { econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*     { rewrite tc_lt in *. lia. } *)
(*   + irw. econs; eauto. *)
(*     { econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*     { rewrite tc_lt in *. lia. } *)
(*   + irw. econs; eauto. *)
(*     { econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*   + irw. econs; eauto. *)
(*     { econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*     { rewrite tc_lt in *. lia. } *)
(*   + irw. econs; eauto. *)
(*     { econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*     { rewrite tc_lt in *. lia. } *)
(*   + irw. econs; eauto. *)
(*     { econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*   + irw. econs; eauto. *)
(*     { econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*     { rewrite tc_lt in *. lia. } *)
(*   + irw. econs; eauto. *)
(*     { econs 2; eauto with paco. econs; eauto with paco. ii. exploit SIMK; eauto with paco. } *)
(*     { rewrite tc_lt in *. lia. } *)
(* Qed. *)

(* Lemma bindC_spec: bindC <5= gupaco4 (_sim_st lt) (cpn4 (_sim_st lt)). *)
(* Proof. *)
(*   intros. eapply wrespect4_uclo; eauto with paco. eapply bindC_wrespectful. *)
(* Qed. *)






(* Lemma bindC_spec *)
(*       simC *)
(*   : *)
(*     bindC <5= gupaco4 (_simg) (simC) *)
(* . *)
(* Proof. *)
(*   gcofix CIH. intros. destruct PR. *)
(*   punfold SIM. inv SIM. *)
(*   - irw. gbase. eapply SIMK; et. rewrite ! bind_ret_l. gbase. eapply SIMK; et. rr; et. *)
(*   - rewrite ! bind_tau. gstep. econs; eauto. pclearbot. *)
(*     (* gfinal. left. eapply CIH. econstructor; eauto. *) *)
(*     debug eauto with paco. *)
(*   - rewrite ! bind_vis. gstep. econs; eauto. u. ii. repeat spc MATCH. pclearbot. eauto with paco. *)
(*   - rewrite ! bind_vis. gstep. econs; eauto. u. ii. repeat spc MATCH. pclearbot. *)
(*     eauto with paco. *)
(*   - rewrite ! bind_vis. gstep. econs; eauto. *)
(*   - rewrite ! bind_vis. gstep. econs; eauto. *)
(*   - rewrite ! bind_vis. *)
(*     gstep. econs; eauto. ii. exploit SIM0; et. intro T; des_safe. pclearbot. eauto with paco. *)
(*   - rewrite ! bind_vis. rewrite ! bind_tau. *)
(*     gstep. econs; eauto. des. pclearbot. eauto with paco. *)
(*   - rewrite ! bind_vis. rewrite ! bind_tau. *)
(*     gstep. econs; eauto. ii. pclearbot. eauto with paco. *)
(* Qed. *)

(* Global Instance match_itr_bind : *)
(*   HProper ((SALL !-> match_itr) !-> match_itr !-> match_itr) ITree.bind' ITree.bind' *)
(* . *)
(* Proof. *)
(*   red. ginit. *)
(*   { intros. eapply cpn2_wcompat; eauto with paco. } *)
(*   guclo bindC_spec. ii. econs; et. *)
(*   u. ii. *)
(*   exploit H0; et. *)
(*   intro T. eauto with paco. *)
(* Qed. *)






Definition resum_itr E F `{E -< F}: itree E ~> itree F := fun _ itr => interp (fun _ e => trigger e) itr.

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
