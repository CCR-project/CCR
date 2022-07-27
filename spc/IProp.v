Require Import Coqlib.
Require Import String.
Require Import PCM.
Require Import Any.

Set Implicit Arguments.
Set Typeclasses Depth 5.


Create HintDb iprop.
Ltac uipropall :=
  repeat (autounfold with iprop; autorewrite with iprop;
       all_once_fast ltac:(fun H => autounfold with iprop in H; autorewrite with iprop in H); ss).

Section IPROP.
  Context {Σ: GRA.t}.

  Local Notation iPred := (Σ -> Prop).

  Record iProp' :=
    iProp_intro {
        iProp_pred :> iPred;
        iProp_mono: forall r0 r1 (WF: URA.wf r1) (LE: URA.extends r0 r1),
          iProp_pred r0 -> iProp_pred r1;
      }.

  Program Definition Sepconj (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => exists a b, r = URA.add a b /\ P a /\ Q b) _).
  Next Obligation.
    red in LE. des; subst.
    exists H, (H0 ⋅ ctx). rewrite URA.add_assoc. splits; auto.
    eapply iProp_mono; eauto.
    { eapply URA.wf_mon. instantiate(1:=H). r_wf WF. }
    { exists ctx. auto. }
  Qed.

  Program Definition Pure (P: Prop): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun _ => P) _).

  Program Definition Ex {X: Type} (P: X -> iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => exists x, P x r) _).
  Next Obligation.
    esplits. eapply iProp_mono; eauto.
  Qed.

  Program Definition Univ {X: Type} (P: X -> iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => forall x, P x r) _).
  Next Obligation.
    eapply iProp_mono; eauto.
  Qed.

  Program Definition Own (r0: Σ): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r1 => URA.extends r0 r1) _).
  Next Obligation.
    etrans; eauto.
  Qed.

  Program Definition And (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => P r /\ Q r) _).
  Next Obligation.
    splits; auto; eapply iProp_mono; eauto.
  Qed.

  Program Definition Or (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => P r \/ Q r) _).
  Next Obligation.
    des.
    { left. eapply iProp_mono; eauto. }
    { right. eapply iProp_mono; eauto. }
  Qed.

  Program Definition Impl (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r0 => forall r1 (WF: URA.wf r1) (LE: URA.extends r0 r1),
                        URA.wf r1 -> P r1 -> Q r1) _).
  Next Obligation.
    eapply H; eauto. etrans; eauto.
  Qed.

  Program Definition Wand (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => forall rp, URA.wf (r ⋅ rp) -> P rp -> Q (r ⋅ rp)) _).
  Next Obligation.
    eapply iProp_mono; [..|eapply H]; eauto.
    { eapply URA.extends_add; auto. }
    { eapply URA.wf_extends; eauto. eapply URA.extends_add; auto. }
  Qed.

  Program Definition Emp: iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun _ => True) _).

  Program Definition Persistently (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r0 => P (URA.core r0)) _).
  Next Obligation.
    eapply iProp_mono; eauto.
    { eapply URA.wf_core; eauto. }
    { eapply URA.extends_core; eauto. }
  Qed.

  Program Definition Plainly (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => P ε) _).

  Program Definition Later (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro P _).
  Next Obligation.
    eapply iProp_mono; eauto.
  Qed.

  (*** this is deprecated in 1.1 ***)
  Program Definition WeakUpd (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r0 => forall ctx, URA.wf (r0 ⋅ ctx) -> exists r1, URA.wf (r1 ⋅ ctx) /\ P r1) _).
  Next Obligation.
    red in LE. des. subst. hexploit (H (ctx0 ⋅ ctx)).
    { rewrite URA.add_assoc. auto. }
    i. des. esplits; [..|eauto]. eapply URA.wf_mon.
    instantiate (1:=ctx0). r_wf H1.
  Qed.

  Program Definition Upd (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r0 => exists r1, P r1 /\ (forall ctx, URA.wf (r0 ⋅ ctx) -> URA.wf (r1 ⋅ ctx))) _).
  Next Obligation.
    esplits; et. i. eapply H1. r in LE. des. subst. eapply URA.wf_mon; et. instantiate (1:=ctx0). r_wf H2.
  Qed.

  Definition Entails (P Q : iProp') : Prop :=
    Seal.sealing
      "iProp"
      (forall r (WF: URA.wf r), P r -> Q r).

  Hint Rewrite (Seal.sealing_eq "iProp"): iprop.
  #[local] Hint Unfold Sepconj Pure Ex Univ Own And Or Impl Wand Emp Persistently Later Upd Entails: iprop.

  (* BI axioms *)
  Global Program Instance PreOrder_Entails: PreOrder Entails.
  Next Obligation.
  Proof.
    ii. uipropall.
  Qed.
  Next Obligation.
  Proof.
    ii. uipropall. ii. exploit (H r); et.
  Qed.

  Lemma Pure_intro: forall (φ : Prop) (P : iProp'), φ -> Entails P (Pure φ).
  Proof.
    ii. uipropall.
  Qed.

  Lemma Pure_elim: forall (φ : Prop) (P : iProp'), (φ -> Entails (Pure True) P) -> Entails (Pure φ) P.
  Proof.
    ii. uipropall. ii. eapply H in H0; et.
  Qed.

  Lemma And_elim_l: forall P Q : iProp', Entails (And P Q) P.
  Proof.
    ii. uipropall. ii. eapply H.
  Qed.

  Lemma And_elim_r: forall P Q : iProp', Entails (And P Q) Q.
  Proof.
    ii. uipropall. ii. eapply H.
  Qed.

  Lemma And_intro: forall P Q R : iProp', Entails P Q -> Entails P R -> Entails P (And Q R).
  Proof.
    ii. uipropall. ii. split; [eapply H|eapply H0]; et.
  Qed.

  Lemma Or_intro_l: forall P Q : iProp', Entails P (Or P Q).
  Proof.
    ii. uipropall. ii. left. ss.
  Qed.

  Lemma Or_intro_r: forall P Q : iProp', Entails Q (Or P Q).
  Proof.
    ii. uipropall. ii. right. ss.
  Qed.

  Lemma Or_elim: forall P Q R : iProp', Entails P R -> Entails Q R -> Entails (Or P Q) R.
  Proof.
    ii. uipropall. ii. inv H1.
    { eapply H; ss. }
    { eapply H0; ss. }
  Qed.

  Lemma Impl_intro_r: forall P Q R : iProp', Entails (And P Q) R -> Entails P (Impl Q R).
  Proof.
    ii. uipropall. ii. eapply H; et. splits; auto. eapply iProp_mono; eauto.
  Qed.

  Lemma Impl_elim_l: forall P Q R : iProp', Entails P (Impl Q R) -> Entails (And P Q) R.
  Proof.
    ii. uipropall. ii. inv H0. eapply H; et. refl.
  Qed.

  Lemma Univ_intro: forall (A : Type) (P : iProp') (Ψ : A -> iProp'), (forall a : A, Entails P (Ψ a)) -> Entails P (Univ (fun a : A => Ψ a)).
  Proof.
    ii. uipropall. ii. specialize (H x). uipropall. eapply H; et.
  Qed.

  Lemma Univ_elim: forall (A : Type) (Ψ : A -> iProp') (a : A), Entails (Univ (fun a0 : A => Ψ a0)) (Ψ a).
  Proof.
    ii. uipropall.
  Qed.

  Lemma Ex_intro: forall (A : Type) (Ψ : A -> iProp') (a : A), Entails (Ψ a) (Ex (fun a0 : A => Ψ a0)).
  Proof.
    ii. uipropall. ii. eexists. eauto.
  Qed.

  Lemma Ex_elim: forall (A : Type) (Φ : A -> iProp') (Q : iProp'), (forall a : A, Entails (Φ a) Q) -> Entails (Ex (fun a : A => Φ a)) Q.
  Proof.
    ii. uipropall. ii. des. specialize (H x). uipropall. et.
  Qed.

  Lemma Sepconj_mono: forall P P' Q Q' : iProp', Entails P Q -> Entails P' Q' -> Entails (Sepconj P P') (Sepconj Q Q').
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des; subst. esplits; et.
    { eapply H; et. eapply URA.wf_mon; et. }
    { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
  Qed.

  Lemma Emp_Sepconj_l: forall P : iProp', Entails P (Sepconj Emp P).
  Proof.
    ii. uipropall. ii. exists ε, r. splits; ss. rewrite URA.unit_idl. et.
  Qed.

  Lemma Emp_Sepconj_r: forall P : iProp', Entails (Sepconj Emp P) P.
  Proof.
    ii. uipropall. ii. inv H. des; subst. eapply iProp_mono; eauto.
    exists x. r_solve.
  Qed.

  Lemma Sepconj_comm: forall P Q : iProp', Entails (Sepconj P Q) (Sepconj Q P).
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des. subst. exists b, a. splits; et. apply URA.add_comm.
  Qed.

  Lemma Sepconj_assoc: forall P Q R : iProp', Entails (Sepconj (Sepconj P Q) R) (Sepconj P (Sepconj Q R)).
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des; subst. esplits; [|apply H2| |apply H3|apply H1]; ss.
    rewrite URA.add_assoc. ss.
  Qed.

  Lemma Wand_intro_r: forall P Q R : iProp', Entails (Sepconj P Q) R -> Entails P (Wand Q R).
  Proof.
    ii. uipropall. ii. eapply H; et.
  Qed.

  Lemma Wand_elim_l: forall P Q R : iProp', Entails P (Wand Q R) -> Entails (Sepconj P Q) R.
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des; subst. eapply H; et. eapply URA.wf_mon; et.
  Qed.

  Lemma Persistently_mono: forall P Q : iProp', Entails P Q -> Entails (Persistently P) (Persistently Q).
  Proof.
    ii. uipropall. ii. eapply H; eauto. eapply URA.wf_core; eauto.
  Qed.

  Lemma Persistently_idem: forall P : iProp', Entails (Persistently P) (Persistently (Persistently P)).
  Proof.
    ii. uipropall. ii. rewrite URA.core_idem. auto.
  Qed.

  Lemma Persistently_emp: Entails Emp (Persistently Emp).
  Proof.
    uipropall.
  Qed.

  Lemma Persistently_univ: forall (A : Type) (Ψ : A -> iProp'), Entails (Univ (fun a => Persistently (Ψ a))) (Persistently (Univ (fun a => Ψ a))).
  Proof.
    ii. uipropall. ii. specialize (H x). uipropall.
  Qed.

  Lemma Persistently_ex: forall (A : Type) (Ψ : A -> iProp'), Entails (Persistently (Ex (fun a => Ψ a))) (Ex (fun a => Persistently (Ψ a))).
  Proof.
    ii. uipropall. ii. des. exists x. uipropall.
  Qed.

  Lemma Persistently_sep: forall P Q : iProp', Entails (Sepconj (Persistently P) Q) (Persistently P).
  Proof.
    ii. uipropall. ii. des. subst.
    eapply iProp_mono; [..|eauto].
    { eapply URA.wf_core; eauto. }
    { eapply URA.extends_core; eauto. exists b. auto. }
  Qed.

  Lemma Persistently_and: forall P Q : iProp', Entails (And (Persistently P) Q) (Sepconj P Q).
  Proof.
    ii. uipropall. ii. des. esplits; eauto. rewrite URA.core_id. auto.
  Qed.

  Lemma Persistently_and2: forall P Q : iProp', Entails (And (Persistently P) (Persistently Q)) (Persistently (And P Q)).
  Proof.
    ii. uipropall.
  Qed.

  Lemma Upd_intro: forall P : iProp', Entails P (Upd P).
  Proof.
    ii. uipropall. ii. exists r. splits; auto.
  Qed.

  Lemma Upd_mono: forall P Q : iProp', Entails P Q -> Entails (Upd P) (Upd Q).
  Proof.
    ii. uipropall. ii. des. esplits; eauto. eapply H; et. specialize (H1 ε). rewrite ! URA.unit_id in H1. et.
  Qed.

  Lemma Upd_trans: forall P : iProp', Entails (Upd (Upd P)) (Upd P).
  Proof.
    ii. uipropall. ii. des. esplits; et.
  Qed.

  Lemma Upd_frame_r: forall P R : iProp', Entails (Sepconj (Upd P) R) (Upd (Sepconj P R)).
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des. subst. esplits; et. i.
    rewrite <- URA.add_assoc in H. eapply H2 in H. r_wf H.
  Qed.
End IPROP.
Hint Rewrite (Seal.sealing_eq "iProp"): iprop.
#[export] Hint Unfold Sepconj Pure Ex Univ Own And Or Impl Wand Emp Persistently Later Upd Entails: iprop.
