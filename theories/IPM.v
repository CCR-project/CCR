From iris.bi Require Import derived_connectives updates internal_eq plainly.
From iris.prelude Require Import options.

Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import PCM.
Require Import Any.
Require Import ITreelib.

Set Implicit Arguments.
Set Typeclasses Depth 5.



Section IRIS.
  Context {Σ: GRA.t}.
  Definition iProp := Σ -> Prop.

  Definition Sepconj (P Q: iProp): iProp :=
    fun r => exists a b, r = URA.add a b /\ P a /\ Q b
  .
  Definition Pure (P: Prop): iProp := fun _ => P.
  Definition Ex {X: Type} (P: X -> iProp): iProp := fun r => exists x, P x r.
  Definition Univ {X: Type} (P: X -> iProp): iProp := fun r => forall x, P x r.
  Definition Own (r0: Σ): iProp := fun r1 => URA.extends r0 r1.
  Definition And (P Q: iProp): iProp := fun r => P r /\ Q r.
  Definition Or (P Q: iProp): iProp := fun r => P r \/ Q r.
  Definition Impl (P Q: iProp): iProp := fun r => URA.wf r -> P r -> Q r.
  Definition Wand (P Q: iProp): iProp := fun r => forall rp, URA.wf (r ⋅ rp) -> P rp -> Q (r ⋅ rp).


  Inductive Entails (P Q : iProp) : Prop :=
    { iProp_entails :> forall r (WF: URA.wf r), P r -> Q r }.

  (* Definition Entails (P Q: iProp): Prop := forall r (WF: URA.wf r), P r -> Q r. *)

  Definition Upd (P: iProp): iProp := fun r0 => forall ctx, URA.wf (r0 ⋅ ctx) -> exists r1, URA.wf (r1 ⋅ ctx) /\ P r1.

  Definition Emp: iProp := eq ε.
  Definition Persistently (P: iProp): iProp := Pure (P ε).
  Definition Later (P: iProp): iProp := P.

  (* Trivial Ofe Structure *)
  Inductive uPred_equiv' (P Q : iProp) : Prop :=
    { uPred_in_equiv : ∀ x, URA.wf x -> P x <-> Q x }.

  Local Instance uPred_equiv : Equiv iProp := uPred_equiv'.
  Definition uPred_dist' (n : nat) (P Q : iProp) : Prop := uPred_equiv' P Q.
  Local Instance uPred_dist : Dist iProp := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin iProp.
  Proof.
    split.
    - intros P Q; split.
      + ii. ss.
      + ii. specialize (H 0). ss.
    - i. split.
      + ii. ss.
      + ii. econs. i. symmetry. apply H. auto.
      + ii. econs. i. transitivity (y x0); [apply H|apply H0]; ss.
    - i. ss.
  Qed.
  Canonical Structure uPredO : ofe := Ofe iProp uPred_ofe_mixin.

  Program Definition uPred_compl : Compl uPredO := λ c x, forall n, c n x.

  Global Program Instance uPred_cofe : Cofe uPredO := {| compl := uPred_compl |}.
  Next Obligation.
    econs. i. split.
    - ii. exploit H0; et.
    - ii. destruct (le_ge_dec n n0).
      + apply c in l. apply l in H0; et.
      + apply c in g. apply g in H0; et.
  Qed.

  (* BI axioms *)
  Global Program Instance PreOrder_Entails: PreOrder Entails.
  Next Obligation.
  Proof.
    ii. ss.
  Qed.
  Next Obligation.
  Proof.
    ii. econs. ii. exploit (H r); et. eapply H0. auto.
  Qed.

  Lemma Pure_intro: ∀ (φ : Prop) (P : iProp), φ → Entails P (Pure φ).
  Proof.
    ii. ss.
  Qed.

  Lemma Pure_elim: ∀ (φ : Prop) (P : iProp), (φ → Entails (Pure True) P) → Entails (Pure φ) P.
  Proof.
    ii. econs. ii. eapply H in H0. eapply H0; ss.
  Qed.

  Lemma And_elim_l: ∀ P Q : iProp, Entails (And P Q) P.
  Proof.
    ii. econs. ii. eapply H.
  Qed.

  Lemma And_elim_r: ∀ P Q : iProp, Entails (And P Q) Q.
  Proof.
    ii. econs. ii. eapply H.
  Qed.

  Lemma And_intro: ∀ P Q R : iProp, Entails P Q → Entails P R → Entails P (And Q R).
  Proof.
    ii. econs. ii. split; [eapply H|eapply H0]; et.
  Qed.

  Lemma Or_intro_l: ∀ P Q : iProp, Entails P (Or P Q).
  Proof.
    ii. econs. ii. left. ss.
  Qed.

  Lemma Or_intro_r: ∀ P Q : iProp, Entails Q (Or P Q).
  Proof.
    ii. econs. ii. right. ss.
  Qed.

  Lemma Or_elim: ∀ P Q R : iProp, Entails P R → Entails Q R → Entails (Or P Q) R.
  Proof.
    ii. econs. ii. inv H1.
    { eapply H; ss. }
    { eapply H0; ss. }
  Qed.

  Lemma Impl_intro_r: ∀ P Q R : iProp, Entails (And P Q) R → Entails P (Impl Q R).
  Proof.
    ii. econs. ii. eapply H; et. split; ss.
  Qed.

  Lemma Impl_elim_l: ∀ P Q R : iProp, Entails P (Impl Q R) → Entails (And P Q) R.
  Proof.
    ii. econs. ii. inv H0. eapply H; et.
  Qed.

  Lemma Univ_intro: ∀ (A : Type) (P : iProp) (Ψ : A → iProp), (∀ a : A, Entails P (Ψ a)) → Entails P (Univ (λ a : A, Ψ a)).
  Proof.
    ii. econs. ii. eapply H; et.
  Qed.

  Lemma Univ_elim: ∀ (A : Type) (Ψ : A → iProp) (a : A), Entails (Univ (λ a0 : A, Ψ a0)) (Ψ a).
  Proof.
    ii. econs. ii. eapply H; et.
  Qed.

  Lemma Ex_intro: ∀ (A : Type) (Ψ : A → iProp) (a : A), Entails (Ψ a) (Ex (λ a0 : A, Ψ a0)).
  Proof.
    ii. econs. ii. eexists. eauto.
  Qed.

  Lemma Ex_elim: ∀ (A : Type) (Φ : A → iProp) (Q : iProp), (∀ a : A, Entails (Φ a) Q) → Entails (Ex (λ a : A, Φ a)) Q.
  Proof.
    ii. econs. ii. inv H0. eapply H; et.
  Qed.

  Lemma Sepconj_mono: ∀ P P' Q Q' : iProp, Entails P Q → Entails P' Q' → Entails (Sepconj P P') (Sepconj Q Q').
  Proof.
    ii. econs. ii. unfold Sepconj in *. des; subst. esplits; et.
    { eapply H; et. eapply URA.wf_mon; et. }
    { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
  Qed.

  Lemma Emp_Sepconj_l: ∀ P : iProp, Entails P (Sepconj Emp P).
  Proof.
    ii. econs. ii. exists ε, r. splits; ss. rewrite URA.unit_idl. et.
  Qed.

  Lemma Emp_Sepconj_r: ∀ P : iProp, Entails (Sepconj Emp P) P.
  Proof.
    ii. econs. ii. inv H. des; subst. inv H1. rewrite URA.unit_idl. et.
  Qed.

  Lemma Sepconj_comm: ∀ P Q : iProp, Entails (Sepconj P Q) (Sepconj Q P).
  Proof.
    ii. econs. ii. unfold Sepconj in *. des. subst. exists b, a. splits; et. apply URA.add_comm.
  Qed.

  Lemma Sepconj_assoc: ∀ P Q R : iProp, Entails (Sepconj (Sepconj P Q) R) (Sepconj P (Sepconj Q R)).
  Proof.
    ii. econs. ii. unfold Sepconj in *. des; subst. esplits; [|apply H2| |apply H3|apply H1]; ss.
    rewrite URA.add_assoc. ss.
  Qed.

  Lemma Wand_intro_r: ∀ P Q R : iProp, Entails (Sepconj P Q) R → Entails P (Wand Q R).
  Proof.
    ii. econs. ii. eapply H; et. exists r, rp. splits; et.
  Qed.

  Lemma Wand_elim_l: ∀ P Q R : iProp, Entails P (Wand Q R) → Entails (Sepconj P Q) R.
  Proof.
    ii. econs. ii. unfold Sepconj in *. des; subst. eapply H; et. eapply URA.wf_mon; et.
  Qed.

  Lemma Upd_intro: ∀ P : iProp, Entails P (Upd P).
  Proof.
    ii. econs. ii. exists r. splits; auto.
  Qed.

  Lemma Upd_mono: ∀ P Q : iProp, Entails P Q -> Entails (Upd P) (Upd Q).
  Proof.
    ii. econs. ii. exploit H0; et. i. des.
    exploit (H r1); et. eapply URA.wf_mon; et.
  Qed.

  Lemma Upd_trans: ∀ P : iProp, Entails (Upd (Upd P)) (Upd P).
  Proof.
    ii. econs. ii. exploit H; et. i. des. exploit x0; eauto.
  Qed.

  Lemma Upd_frame_r: ∀ P R : iProp, Entails (Sepconj (Upd P) R) (Upd (Sepconj P R)).
  Proof.
    ii. econs. ii. unfold Sepconj in *. des. subst. exploit (H1 (b ⋅ ctx)); et.
    { rewrite URA.add_assoc. et. }
    i. des. esplits; [..|eapply x1|eapply H2]; ss.
    rewrite <- URA.add_assoc. et.
  Qed.

  Lemma iProp_bi_mixin:
    BiMixin
      Entails Emp Pure And Or Impl
      (@Univ) (@Ex) Sepconj Wand
      Persistently.
  Proof.
    econs.
    - exact PreOrder_Entails.
    - econs.
      { ii. split; econs; ii; eapply H; et. }
      { split. des. i. split; i.
        { eapply H; et. }
        { eapply H0; et. }
      }
    - econs. i. split.
      { ii. eapply H. ss. }
      { ii. eapply H. ss. }
    - econs. i. split.
      { ii. inv H2. split.
        { eapply H; et. }
        { eapply H0; et. }
      }
      { ii. inv H2. split.
        { eapply H; et. }
        { eapply H0; et. }
      }
    - econs. i. split.
      { ii. inv H2.
        { left. eapply H; et. }
        { right. eapply H0; et. }
      }
      { ii. inv H2.
        { left. eapply H; et. }
        { right. eapply H0; et. }
      }
    - econs. i. split.
      { ii. eapply H0; et. eapply H2; et. eapply H; et. }
      { ii. eapply H0; et. eapply H2; et. eapply H; et. }
    - econs. i. split.
      { ii. exploit H; et. i. eapply x2; et. }
      { ii. exploit H; et. i. eapply x2; et. }
    - econs. i. split.
      { ii. inv H1. exploit H; et. i. eexists. eapply x2; et. }
      { ii. inv H1. exploit H; et. i. eexists. eapply x2; et. }
    - econs. i. split.
      { ii. inv H2. des. subst. eexists. esplits; eauto.
        { eapply H; et. eapply URA.wf_mon; et. }
        { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
      }
      { ii. inv H2. des. subst. eexists. esplits; eauto.
        { eapply H; et. eapply URA.wf_mon; et. }
        { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
      }
    - econs. i. split.
      { ii. exploit H2; et.
        { eapply H; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
        { i. eapply H0; et. }
      }
      { ii. exploit H2; et.
        { eapply H; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
        { i. eapply H0; et. }
      }
    - ii. econs. i. split.
      { ii. eapply H; ss. eapply URA.wf_unit. }
      { ii. eapply H; ss. eapply URA.wf_unit. }
    - exact Pure_intro.
    - exact Pure_elim.
    - exact And_elim_l.
    - exact And_elim_r.
    - exact And_intro.
    - exact Or_intro_l.
    - exact Or_intro_r.
    - exact Or_elim.
    - exact Impl_intro_r.
    - exact Impl_elim_l.
    - exact Univ_intro.
    - exact Univ_elim.
    - exact Ex_intro.
    - exact Ex_elim.
    - exact Sepconj_mono.
    - exact Emp_Sepconj_l.
    - exact Emp_Sepconj_r.
    - exact Sepconj_comm.
    - exact Sepconj_assoc.
    - exact Wand_intro_r.
    - exact Wand_elim_l.
    - ii. econs; ii. eapply H; et. eapply URA.wf_unit.
    - ii. econs; ii. eapply H; et.
    - ii. econs; ii. red in H. subst. ss.
    - ii. econs; ii. eapply H; et.
    - ii. econs; ii. inv H. exists x. ss.
    - ii. econs; ii. unfold Sepconj in *. des; subst. ss.
    - ii. econs; ii. inv H. unfold Sepconj in *. esplits; et. rewrite URA.unit_idl. et.
  Qed.

  Lemma iProp_bi_later_mixin:
    BiLaterMixin
      Entails Pure Or Impl
      (@Univ) (@Ex) Sepconj Persistently Later.
  Proof.
    econs.
    - ii. econs. i. split.
      { i. eapply H; et. }
      { i. eapply H; et. }
    - ii. eapply H; et.
    - ii. ss.
    - ii. econs; ii. eapply H.
    - ii. econs; ii. right. ss.
    - ii. ss.
    - ii. ss.
    - ii. ss.
    - ii. ss.
    - ii. econs; ii. right. ss.
  Qed.

  Canonical Structure iPropI: bi :=
    {| bi_bi_mixin := iProp_bi_mixin;
       bi_bi_later_mixin := iProp_bi_later_mixin |}.

  (** extra BI instances *)
  Lemma iProp_bupd_mixin: BiBUpdMixin iPropI Upd.
  Proof.
    econs.
    - ii. econs. i. split.
      { ii. exploit H1; eauto. i. des. esplits; eauto.
        eapply H; et. eapply URA.wf_mon; et. }
      { ii. exploit H1; eauto. i. des. esplits; eauto.
        eapply H; et. eapply URA.wf_mon; et. }
    - exact Upd_intro.
    - exact Upd_mono.
    - exact Upd_trans.
    - exact Upd_frame_r.
  Qed.
  Global Instance iProp_bi_bupd: BiBUpd iPropI := {| bi_bupd_mixin := iProp_bupd_mixin |}.

  Global Instance iProp_bupd_absorbing (P: iPropI): Absorbing (bupd P).
  Proof.
    ii. econs; ii. red in H. inv H. des. subst. exploit H3; et.
    eapply URA.wf_mon. rewrite URA.add_comm. rewrite URA.add_assoc. et.
  Qed.

  Global Instance iProp_pure_forall: BiPureForall iPropI.
  Proof.
    ii. econs; ii. eapply H.
  Qed.


  From iris.proofmode Require Export tactics class_instances.

  (** AsEmpValid *)
  Global Instance as_emp_valid_emp_valid (P: iPropI) : AsEmpValid0 (⊢ P) P | 0.
  Proof. by rewrite /AsEmpValid. Qed.
  Global Instance as_emp_valid_entails (P Q: iPropI) : AsEmpValid0 (P ⊢ Q) (P -∗ Q).
  Proof. split; [ apply bi.entails_wand | apply bi.wand_entails ]. Qed.
  Global Instance as_emp_valid_equiv (P Q: iPropI) : AsEmpValid0 (P ≡ Q) (P ∗-∗ Q).
  Proof. Admitted.

  Goal forall (P Q: iPropI), bi_entails (bi_sep (bupd P) Q) (bupd Q).
  Proof.
    i. iStartProof.
    iIntros "[Hxs Hys]". iMod "Hxs". iApply "Hys".
  Qed.

  Variable P Q R: iProp.
  Hypothesis PQ: bi_entails P Q.
  Hypothesis QR: bi_entails Q R.


  From stdpp Require Import namespaces hlist pretty.
  From iris.bi Require Export bi telescopes.
  From iris.proofmode Require Import base intro_patterns spec_patterns
       sel_patterns coq_tactics reduction.
  From iris.proofmode Require Export classes notation.
  From iris.prelude Require Import options.
  Export ident.

  From iris.proofmode Require Import tactics ltac_tactics.


  Local Ltac iApplyHypExact H :=
    eapply tac_assumption with H _ _; (* (i:=H) *)
    [pm_reflexivity
    |iSolveTC
    |pm_reduce; iSolveTC ||
                         fail 1 "iApply: remaining hypotheses not affine and the goal not absorbing"].

  Local Ltac iApplyHypLoop H :=
    first
      [eapply tac_apply with H _ _ _;
       [pm_reflexivity
       |iSolveTC
       |pm_reduce;
        pm_prettify (* reduce redexes created by instantiation *)]].

  Tactic Notation "iApplyHyp" constr(H) :=
    first
      [iApplyHypExact H
      |iApplyHypLoop H
      |lazymatch iTypeOf H with
       | Some (_,?Q) => fail 1 "iApply: cannot apply" Q
       end].

  Tactic Notation "iApply" open_constr(lem) :=
    iPoseProofCore lem as false (fun H => iApplyHyp H).


  Tactic Notation "iPoseProofCoreHyp" constr(H) "as" constr(Hnew) :=
    let Δ := iGetCtx in
    notypeclasses refine (tac_pose_proof_hyp _ H Hnew _ _);
    pm_reduce;
    lazymatch goal with
    | |- False =>
      let lookup := pm_eval (envs_lookup_delete false H Δ) in
      lazymatch lookup with
      | None =>
        let H := pretty_ident H in
        fail "iPoseProof:" H "not found"
      | _ =>
        let Hnew := pretty_ident Hnew in
        fail "iPoseProof:" Hnew "not fresh"
      end
    | _ => idtac
    end.

  Tactic Notation "iPoseProofCoreLem" open_constr(lem) "as" tactic3(tac) :=
    let Hnew := iFresh in
    notypeclasses refine (tac_pose_proof _ Hnew _ _ (into_emp_valid_proj _ _ _ lem) _);
    [iIntoEmpValid
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let Hnew := pretty_ident Hnew in
       fail "iPoseProof:" Hnew "not fresh"
     | _ => tac Hnew
     end];
    (* Solve all remaining TC premises generated by [iIntoEmpValid] *)
    try iSolveTC.

  Tactic Notation "iPoseProofCore" open_constr(lem)
         "as" constr(p) tactic3(tac) :=
    iStartProof;
    let t := lazymatch lem with ITrm ?t ?xs ?pat => t | _ => lem end in
    let t := lazymatch type of t with string => constr:(INamed t) | _ => t end in
    let spec_tac Htmp :=
        lazymatch lem with
        | ITrm _ ?xs ?pat => iSpecializeCore (ITrm Htmp xs pat) as p
        | _ => idtac
        end in
    pose t
  .
    (* lazymatch type of t with *)
    (* | _ => iPoseProofCoreLem t as (fun Htmp => spec_tac Htmp; [..|tac Htmp]) *)
    (* end. *)



  Ltac iIntoEmpValid_go := first
                             [(* Case [φ → ψ] *)
                               notypeclasses refine (into_emp_valid_impl _ _ _ _ _);
                               [(*goal for [φ] *)|iIntoEmpValid_go]
                              |(* Case [∀ x : A, φ] *)
                              notypeclasses refine (into_emp_valid_forall _ _ _ _); iIntoEmpValid_go
                              |(* Case [∀.. x : TT, φ] *)
                              notypeclasses refine (into_emp_valid_tforall _ _ _ _); iIntoEmpValid_go
                              |(* Case [P ⊢ Q], [P ⊣⊢ Q], [⊢ P] *)
                              notypeclasses refine (into_emp_valid_here _ _ _)].

  Ltac iIntoEmpValid :=
    (* Factor out the base case of the loop to avoid needless backtracking *)
    iIntoEmpValid_go;
    [.. (* goals for premises *)
    |iSolveTC ||
              let φ := lazymatch goal with |- AsEmpValid ?φ _ => φ end in
              fail "iPoseProof:" φ "not a BI assertion"].


  Goal bi_entails P R.
  Proof.
    i. iStartProof. iIntros "H".
    Show Proof.
    Set Printing All.

    let Hnew := iFresh in
    notypeclasses refine (tac_pose_proof _ Hnew _ _ (into_emp_valid_proj _ _ _ QR) _).
    {

      refine (into_emp_valid_forall _ _ _ _).

      refine (@into_emp_valid_forall _ _ _ _ _ _).

      iIntoEmpValid_go.

      Local Opaque bi_entails.
      refine (into_emp_valid_forall _ _ _ _).

      @into_emp_valid_forall ?PROP ?A
        : forall (φ : forall _ : ?A, Type) (P0 : bi_car ?PROP) (x : ?A) (_ : @IntoEmpValid ?PROP (φ x) P0),
          @IntoEmpValid ?PROP (forall x0 : ?A, φ x0) P0
      where
      ?PROP : [Σ : GRA.t  P : iProp  Q : iProp  R : iProp  PQ : @bi_entails iPropI P Q  QR : @bi_entails iPropI Q R
               |- bi]
                ?A : [Σ : GRA.t  P : iProp  Q : iProp  R : iProp  PQ : @bi_entails iPropI P Q  QR : @bi_entails iPropI Q R
                      |- Type]


      iIntoEmpValid_go.

    ].


      notypeclasses refine (into_emp_valid_here _ _ _).


      first
        [(* Case [φ → ψ] *)
          notypeclasses refine (into_emp_valid_impl _ _ _ _ _);
          [(*goal for [φ] *)|iIntoEmpValid_go]
         |(* Case [∀ x : A, φ] *)
         notypeclasses refine (into_emp_valid_forall _ _ _ _); iIntoEmpValid_go
         |(* Case [∀.. x : TT, φ] *)
         notypeclasses refine (into_emp_valid_tforall _ _ _ _); iIntoEmpValid_go
         |(* Case [P ⊢ Q], [P ⊣⊢ Q], [⊢ P] *)
         notypeclasses refine (into_emp_valid_here _ _ _)].


      iIntoEmpValid_go.

      ; cycle 2.
      { eapply class_instances.as_emp_valid_entails.
        eapply as_emp_valid_entails.


        eapply as_emp_valid_entails.
        {

        red.        typeclasses eauto.

        solve [ once typeclasses eauto ].
        .
        iSolveTC.

      3:{ iSolveTC.
        [.. (* goals for premises *)
        |iSolveTC ||
                  let φ := lazymatch goal with |- AsEmpValid ?φ _ => φ end in
                  fail "iPoseProof:" φ "not a BI assertion"].

      iIntoEmpValid.




      let Hnew := iFresh in
      notypeclasses refine (tac_pose_proof _ Hnew _ _ (into_emp_valid_proj _ _ _ QR) _).

      [iIntoEmpValid
      |pm_reduce;
       lazymatch goal with
       | |- False =>
         let Hnew := pretty_ident Hnew in
         fail "iPoseProof:" Hnew "not fresh"
       | _ => iApplyHyp Hnew
       end];
      (* Solve all remaining TC premises generated by [iIntoEmpValid] *)
      try iSolveTC.


    iPoseProofCoreLem QR as (fun Htmp => iApplyHyp Htmp).




    end.


    iStartProof;
      let t := lazymatch QR with ITrm ?t ?xs ?pat => t | _ => QR end in
      let t := lazymatch type of t with string => constr:(INamed t) | _ => t end in
      let spec_tac Htmp :=
          lazymatch QR with
          | ITrm _ ?xs ?pat => iSpecializeCore (ITrm Htmp xs pat) as false
          | _ => idtac
          end in
      lazymatch type of QR with
      | _ => iPoseProofCoreLem QR as (fun Htmp => idtac Htmp; [..|iApplyHyp Htmp])
      end.


    iApply QR. iApply H. iApply H0. iApply H in "H".

    iIntros "[Hxs Hys]". iMod "Hys". iApply "Hxs".
  Qed.

End IRIS.

From iris.proofmode Require Export tactics.

Section IRIS.
  Context {Σ: GRA.t}.

  Variable P Q R: iPropI.
  Hypothesis PQ: bi_entails P Q.
  Hypothesis QR: bi_entails Q R.

  Goal bi_entails P R.
  Proof.
    i. iStartProof. iIntros "H".
    Set Printing All.
    iApply QR. iApply H. iApply H0. iApply H in "H".

    iIntros "[Hxs Hys]". iMod "Hys". iApply "Hxs".
  Qed.



End IRIS.
