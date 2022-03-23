Require Import sflib.
Require Import Coqlib.
Require Import STS.
Require Import Behavior.

Set Implicit Arguments.

Section VISNORM.

  Definition norm_state state : state -> state * (option event) :=
    fun old => (old, None).

  Definition norm_state_sort state state_sort :
    (state * (option event)) -> sort :=
    fun '(st, ev) =>
      match ev with
      | None =>
        match (state_sort st) with
        | vis => demonic
        | _ => (state_sort st)
        end
      | _ => vis
      end
  .

  (** normalization in 2-fold:
      1. make vis states deterministic
      2. erase vis states with 'None' event *)
  Inductive norm_step state state_sort step :
    (state * (option event)) -> option event -> (state * (option event)) -> Prop :=
  | step_vis_before
      st0 ev st1
      (VIS: state_sort st0 = vis)
      (STEP: step st0 (Some ev) st1)
    :
      norm_step state_sort step (st0, None) None (st0, Some ev)

  | step_vis_after
      st0 ev st1
      (VIS: state_sort st0 = vis)
      (STEP: step st0 (Some ev) st1)
      (HALF: norm_step state_sort step (st0, None) None (st0, Some ev))
    :
      norm_step state_sort step (st0, Some ev) (Some ev) (st1, None)

  | step_else
      st0 st1
      (NOVIS: state_sort st0 <> vis)
      (STEP: step st0 None st1)
    :
      norm_step state_sort step (st0, None) None (st1, None)
  .

  Program Definition vis_normalize (L: semantics) : semantics := {|
    state := (L.(state) * (option event));
    step := (norm_step L.(state_sort) L.(step));
    initial_state := (norm_state L.(initial_state));
    state_sort := (norm_state_sort L.(state_sort));
  |}.
  Next Obligation.
    inv VIS. destruct o1; clarify.
    - inv STEP; inv STEP0; ss; clarify.
      assert (s0 = s).
      { eapply wf_vis; eauto. }
      subst; auto.
    - destruct (state_sort L s1); ss; clarify.
  Qed.
  Next Obligation.
    inv VIS. destruct o0; clarify.
    - inv STEP; ss; clarify.
    - destruct (state_sort L s0); ss; clarify.
  Qed.
  Next Obligation.
    inv VIS. destruct o0; clarify. destruct (state_sort L s0) eqn:EQ; ss; clarify.
    inv STEP; ss; clarify.
  Qed.
  Next Obligation.
    inv VIS. destruct o0; clarify.
    destruct (state_sort L s0) eqn:EQ; ss; clarify; inv STEP; ss; clarify.
  Qed.
  Next Obligation.
    inv FIN. destruct o0; clarify. des_ifs.
    inv STEP; ss; rewrite Heq in *; clarify.
    hexploit L.(wf_final); et.
  Qed.

  Definition vis_normalized (L: semantics) :=
    exists L', L = vis_normalize L'.

  Lemma wf_vis_norm :
    forall (L: semantics) st0 ev0 ev1 st1 st2,
      vis_normalized L ->
      L.(state_sort) st0 = vis ->
      L.(step) st0 ev0 st1 -> L.(step) st0 ev1 st2 ->
      (ev0 = ev1) /\ (st1 = st2).
  Proof.
    i. unfold vis_normalized in H. des.
    unfold vis_normalize in H; ss; clarify.
    inv H0; ss; clarify.
    unfold norm_state_sort in H3.
    destruct st0. destruct o; ss; clarify.
    inv H1; inv H2; ss; clarify.
    - split; auto.
      assert (st3 = st1).
      { eapply wf_vis; eauto. }
      ss; clarify.
    - destruct (state_sort L' s); clarify.
  Qed.

End VISNORM.

Section PROOF.

  Import Behavior.Beh.

  Lemma beh_preserved_dir_spin:
    forall (L: semantics) st0,
      state_spin (vis_normalize L) (norm_state st0) ->
      state_spin L st0.
  Proof.
    i. generalize dependent st0. pcofix CIH. i.
    punfold H0. inv H0.
    + ss. destruct (state_sort L st0) eqn:EQ; clarify. clear SRT.
      pfold. econs; auto. i.
      assert (ev = None).
      { eapply wf_angelic; eauto. }
      clarify.
      specialize (STEP None (st1, None)).
      destruct STEP.
      * econs 3; auto. unfold not. i. rewrite H in EQ; clarify.
      * right. apply CIH. apply H.
      * clarify.
    + des.
      assert (ev = None).
      { eapply wf_demonic; eauto. }
      subst.
      ss. destruct (state_sort L st0) eqn:EQ; clarify; clear SRT.
      * pfold. econs 2; auto.
        inv STEP0; try (rewrite VIS in EQ; inv EQ).
        exists None, st3, STEP. right. apply CIH. inv TL; clarify.
      * inv STEP0.
        2:{ apply NOVIS in EQ. clarify. }
        pfold. inv TL; clarify. punfold H.
        2:{ assert( monotone1 (_state_spin (vis_normalize L))).
            { eauto with paco. }
            ss. }
        inv H; ss.
  Qed.

  Theorem beh_preserved_dir:
    forall (L: semantics) st0 tr,
      of_state (vis_normalize L) (norm_state st0) tr ->
      of_state L st0 tr.
  Proof.
    intros L. pcofix CIH. i. pfold. punfold H0.
    remember (norm_state st0) as st0'.
    generalize dependent st0.
    induction H0 using of_state_ind; i; ss; clarify.
    - econs. unfold norm_state in H. unfold norm_state_sort in H.
      destruct (state_sort L st1); clarify.
    - econs. apply beh_preserved_dir_spin; auto.
    - ss. destruct (state_sort L st2); clarify.
    - ss. destruct (state_sort L st1) eqn:EQ; clarify; clear SRT.
      + unfold union in STEP. des. clarify.
        inv STEP0.
        { rewrite VIS in EQ; clarify. }
        clear NOVIS. econs 5; auto.
        exists None, st3. repeat (split; auto).
      + unfold union in STEP. des. clarify.
        inv STEP0.
        2:{ apply NOVIS in EQ; clarify. }
        clear VIS.
        inv TL; clarify.
        { punfold SPIN. inv SPIN; clarify. }
        ss. clear SRT.
        inv STEP0; ss; clarify.
        econs; eauto. right. apply CIH. inv TL0; clarify.
    - ss. destruct (state_sort L st1) eqn:EQ; clarify; clear SRT.
      econs 6; auto.
      unfold inter in *. i. split.
      { exploit wf_angelic; eauto. }
      assert (ev = None).
      { exploit wf_angelic; eauto. }
      subst.
      specialize (STEP None (st0, None)). ss. unfold norm_state in STEP.
      exploit STEP.
      + econs; auto. unfold not. i. rewrite H in EQ. clarify.
      + i. des. clear HD. eauto.
  Qed.

  Lemma beh_preserved_inv_spin:
    forall (L: semantics) st0,
      state_spin L st0 ->
      state_spin (vis_normalize L) (norm_state st0).
  Proof.
    i. generalize dependent st0. pcofix CIH. i.
    pfold. punfold H0. inv H0.
    - econs.
      { ss. rewrite SRT. reflexivity. }
      i. inv STEP0; ss; clarify.
      { rewrite VIS in SRT; clarify. }
      exploit STEP; eauto. i.
      right. apply CIH. inv x0; clarify.
    - des. econs 2.
      { ss. rewrite SRT. reflexivity. }
      assert (ev = None).
      { exploit wf_demonic; eauto. }
      subst. exists None, (st1, None). eexists.
      { ss. econs; auto.
        unfold not; i. rewrite H in SRT; clarify. }
      right. apply CIH. inv TL; clarify.
  Qed.

  Theorem beh_preserved_inv:
    forall (L: semantics) st0 tr,
      of_state L st0 tr ->
      of_state (vis_normalize L) (norm_state st0) tr.
  Proof.
    intros L. pcofix CIH. i. pfold. punfold H0.
    remember st0 as st'. generalize dependent st0.
    induction H0 using of_state_ind; i; ss; clarify.
    - econs. ss. rewrite H. reflexivity.
    - econs. apply beh_preserved_inv_spin. auto.
    - econs 5.
      { ss. rewrite SRT. reflexivity. }
      exists None, (st2, Some ev). repeat (split; auto).
      + ss. econs; eauto.
      + econs; ss; clarify.
        * econs; eauto. econs; eauto.
        * right. apply CIH. inv TL; clarify.
    - econs.
      { ss. rewrite SRT. reflexivity. }
      unfold union in STEP. des; clarify.
      exists None, (st0, None). repeat (split; eauto).
      econs; eauto. unfold not; i. rewrite H in SRT; clarify.
    - econs 6.
      { ss. rewrite SRT. reflexivity. }
      unfold inter in *. i.
      inv STEP0; ss; clarify.
      { rewrite VIS in SRT; clarify. }
      split; auto.
      specialize (STEP None st3).
      exploit STEP; eauto. i. des.
      eapply IH; eauto.
  Qed.

  Theorem beh_preserved:
    forall (L: semantics) st0 tr,
      of_state L st0 tr <->
      of_state (vis_normalize L) (norm_state st0) tr.
  Proof.
    split.
    - apply beh_preserved_inv.
    - apply beh_preserved_dir.
  Qed.

End PROOF.
