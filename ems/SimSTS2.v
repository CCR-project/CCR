Require Import Coqlib.
Require Import STS.
Require Import Behavior.

Set Implicit Arguments.

Section BEHAVES.

Variable L: semantics.

Theorem of_state_ind2 :
forall (P: _ -> _ -> Prop),
(forall st0 retv, state_sort L st0 = final retv -> P st0 (Tr.done retv)) ->
(forall st0, Beh.state_spin L st0 -> P st0 Tr.spin) ->
(forall st0, P st0 Tr.nb) ->

(forall st0 st1 ev evs
 (SRT: state_sort L st0 = vis)
 (STEP: _.(step) st0 (Some ev) st1)
 (TL: Beh.of_state L st1 evs)
  ,
    P st0 (Tr.cons ev evs)) ->
(forall st0 evs
 (SRT: state_sort L st0 = demonic)
 (STEP: Beh.union L st0
   (fun e st1 =>
    <<HD: e = None >> /\ <<TL: Beh.of_state L st1 evs >> /\ <<IH: P st1 evs>>)), P st0 evs) ->
(forall st0 evs
        (* (IH: forall st1 (STEP: L.(step) st0 None st1), P st1 evs) *)
 (SRT: state_sort L st0 = angelic)
 (STEP: Beh.inter L st0
   (fun e st1 => <<HD: e = None >> /\ <<TL: Beh.of_state L st1 evs >> /\ <<IH: P st1 evs>>)),
 P st0 evs) ->
forall s t, Beh.of_state L s t -> P s t.
Proof.
  i. eapply Beh.of_state_ind; eauto.
  { i. eapply H3; eauto.
    unfold Beh.union in *. des. esplits; eauto.
    pfold. eapply Beh.of_state_mon; eauto.
  }
  { i. eapply H4; eauto. ii. exploit STEP; eauto.
    i. des. esplits; eauto.
    pfold. eapply Beh.of_state_mon; eauto.
  }
  { punfold H5. eapply Beh.of_state_mon; eauto.
    i. pclearbot. auto.
  }
Qed.

Variant indC (of_state: L.(state) -> Tr.t -> Prop): L.(state) -> Tr.t -> Prop :=
| indC_final
    st0 retv
    (FINAL: L.(state_sort) st0 = final retv)
  :
    indC of_state st0 (Tr.done retv)
| indC_spin
    st0
    (SPIN: Beh.state_spin L st0)
  :
    indC of_state st0 (Tr.spin)
| indC_nb
    st0
  :
    indC of_state st0 (Tr.nb)
| indC_vis
    st0 st1 ev evs
    (SRT: L.(state_sort) st0 = vis)
    (STEP: _.(step) st0 (Some ev) st1)
    (TL: of_state st1 evs)
  :
    indC of_state st0 (Tr.cons ev evs)
| indC_demonic
    st0
    evs
    (SRT: L.(state_sort) st0 = demonic)
    (STEP: Beh.union L st0 (fun e st1 => (<<HD: e = None>>) /\ (<<TL: of_state st1 evs>>)))
  :
    indC of_state st0 evs
| indC_angelic
    st0
    evs
    (SRT: L.(state_sort) st0 = angelic)
    (STEP: Beh.inter L st0 (fun e st1 => (<<HD: e = None>>) /\ (<<TL: of_state st1 evs>>)))
  :
    indC of_state st0 evs
.

Lemma indC_mon:
  monotone2 indC.
Proof.
  ii. inv IN; eauto.
  - econs 1; eauto.
  - econs 2; eauto.
  - econs 3; eauto.
  - econs 4; eauto.
  - econs 5; eauto. unfold Beh.union in *. des. esplits; eauto.
  - econs 6; eauto. ii. exploit STEP; eauto. i. des. splits; auto.
Qed.
Hint Resolve indC_mon: paco.

Lemma indC_spec:
  indC <3= gupaco2 (Beh._of_state L) (cpn2 (Beh._of_state L)).
Proof.
  eapply wrespect2_uclo; eauto with paco.
  econs; eauto with paco.
  ii. inv PR.
  { econs 1; eauto. }
  { econs 2; eauto. }
  { econs 3; eauto. }
  { econs 4; eauto. eapply rclo2_base. auto. }
  { econs 5; eauto. unfold Beh.union in *. des. esplits; eauto.
    eapply Beh.of_state_mon; eauto. i. eapply rclo2_base. auto.
  }
  { econs 6; eauto. ii. exploit STEP; eauto. i. des. splits; auto.
    eapply Beh.of_state_mon; eauto. i. eapply rclo2_base. auto.
  }
Qed.

End BEHAVES.

Lemma spin_nofinal
      L st0
      (SPIN: Beh.state_spin L st0)
  :
    forall retv, <<NOFIN: L.(state_sort) st0 <> final retv>>
.
Proof.
  punfold SPIN. inv SPIN; ii; rewrite H in *; ss.
Qed.

Lemma spin_novis
      L st0
      (SPIN: Beh.state_spin L st0)
  :
    <<NOFIN: L.(state_sort) st0 <> vis>>
.
Proof.
  punfold SPIN. inv SPIN; ii; rewrite H in *; ss.
Qed.

Lemma spin_astep
      L st0 ev st1
      (SRT: L.(state_sort) st0 = angelic)
      (STEP: _.(step) st0 ev st1)
      (SPIN: Beh.state_spin _ st0)
  :
    <<SPIN: Beh.state_spin _ st1>>
.
Proof.
  exploit wf_angelic; et. i; clarify.
  punfold SPIN. inv SPIN; rewrite SRT in *; ss.
  exploit STEP0; et. i; des. pclearbot. et.
Qed.



Section SIM.

  Variable L0 L1: semantics.

  Inductive _sim (sim: bool -> bool -> L0.(state) -> L1.(state) -> Prop)
            (i_src0: bool) (i_tgt0: bool) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | sim_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0
  | sim_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          exists i_src1, <<SIM: _sim sim i_src1 i_tgt0 st_src1 st_tgt0>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0
  | sim_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (* (FIN: _.(state_sort) st_src0 = final <-> _.(state_sort) st_tgt0 = final) *)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1)
        ,
          exists i_tgt1, <<SIM: _sim sim i_src0 i_tgt1 st_src0 st_tgt1>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0
  | sim_progress
      (SIM: sim false false st_src0 st_tgt0)
      (SRC: i_src0 = true)
      (TGT: i_tgt0 = true)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0
  .

  Lemma _sim_ind2 sim (P: bool -> bool -> L0.(state) -> L1.(state) -> Prop)
        (FIN: forall
            i_src0 i_tgt0 st_src0 st_tgt0
            retv
            (SRT: _.(state_sort) st_src0 = final retv)
            (SRT: _.(state_sort) st_tgt0 = final retv),
            P i_src0 i_tgt0 st_src0 st_tgt0)
        (DMSRC: forall
            i_src0 i_tgt0 st_src0 st_tgt0
            (SRT: _.(state_sort) st_src0 = demonic)
            (SIM: exists st_src1
                         (STEP: _.(step) st_src0 None st_src1)
              ,
                exists i_src1, <<SIM: _sim sim i_src1 i_tgt0 st_src1 st_tgt0>> /\ <<IH: P i_src1 i_tgt0 st_src1 st_tgt0>>),
            P i_src0 i_tgt0 st_src0 st_tgt0)
        (DMTGT: forall
            i_src0 i_tgt0 st_src0 st_tgt0
            (SRT: _.(state_sort) st_tgt0 = demonic)
            (SIM: forall st_tgt1
                         (STEP: _.(step) st_tgt0 None st_tgt1)
              ,
                exists i_tgt1, <<SIM: _sim sim i_src0 i_tgt1 st_src0 st_tgt1>> /\ <<IH: P i_src0 i_tgt1 st_src0 st_tgt1>>),
            P i_src0 i_tgt0 st_src0 st_tgt0)
        (PROGRESS:
           forall
             i_src0 i_tgt0 st_src0 st_tgt0
             (SIM: sim false false st_src0 st_tgt0)
             (SRC: i_src0 = true)
             (TGT: i_tgt0 = true),
             P i_src0 i_tgt0 st_src0 st_tgt0)
    :
      forall i_src0 i_tgt0 st_src0 st_tgt0
             (SIM: _sim sim i_src0 i_tgt0 st_src0 st_tgt0),
        P i_src0 i_tgt0 st_src0 st_tgt0.
  Proof.
    fix IH 5. i. inv SIM.
    { eapply FIN; eauto. }
    { eapply DMSRC; eauto.
      des. esplits; eauto. }
    { eapply DMTGT; eauto. i.
      hexploit SIM0; eauto. i. des. esplits; eauto. }
    { eapply PROGRESS; eauto. }
  Qed.

  Lemma sim_mon: monotone4 _sim.
  Proof.
    ii. revert x0 x1 x2 x3 IN. eapply _sim_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. des. esplits; eauto. }
    { econs 3; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 4; eauto. }
  Qed.

  Definition sim: _ -> _ -> _ -> _ -> Prop := paco4 _sim bot4.

  Hint Constructors _sim.
  Hint Unfold sim.
  Hint Resolve sim_mon: paco.

  Lemma sim_ind (P: bool -> bool -> L0.(state) -> L1.(state) -> Prop)
        (FIN: forall
            i_src0 i_tgt0 st_src0 st_tgt0
            retv
            (SRT: _.(state_sort) st_src0 = final retv)
            (SRT: _.(state_sort) st_tgt0 = final retv),
            P i_src0 i_tgt0 st_src0 st_tgt0)
        (DMSRC: forall
            i_src0 i_tgt0 st_src0 st_tgt0
            (SRT: _.(state_sort) st_src0 = demonic)
            (SIM: exists st_src1
                         (STEP: _.(step) st_src0 None st_src1)
              ,
                exists i_src1, <<SIM: sim i_src1 i_tgt0 st_src1 st_tgt0>> /\ <<IH: P i_src1 i_tgt0 st_src1 st_tgt0>>),
            P i_src0 i_tgt0 st_src0 st_tgt0)
        (DMTGT: forall
            i_src0 i_tgt0 st_src0 st_tgt0
            (SRT: _.(state_sort) st_tgt0 = demonic)
            (SIM: forall st_tgt1
                         (STEP: _.(step) st_tgt0 None st_tgt1)
              ,
                exists i_tgt1, <<SIM: sim i_src0 i_tgt1 st_src0 st_tgt1>> /\ <<IH: P i_src0 i_tgt1 st_src0 st_tgt1>>),
            P i_src0 i_tgt0 st_src0 st_tgt0)
        (PROGRESS:
           forall
             i_src0 i_tgt0 st_src0 st_tgt0
             (SIM: sim false false st_src0 st_tgt0)
             (SRC: i_src0 = true)
             (TGT: i_tgt0 = true),
             P i_src0 i_tgt0 st_src0 st_tgt0)
    :
      forall i_src0 i_tgt0 st_src0 st_tgt0
             (SIM: sim i_src0 i_tgt0 st_src0 st_tgt0),
        P i_src0 i_tgt0 st_src0 st_tgt0.
  Proof.
    i. eapply (@_sim_ind2 sim P); eauto.
    { i. eapply DMSRC; eauto. des. esplits; eauto.
      pfold. eapply sim_mon; eauto.
    }
    { i. eapply DMTGT; eauto. i. hexploit SIM0; eauto. i. des. esplits; eauto.
      pfold. eapply sim_mon; eauto.
    }
    { punfold SIM. eapply sim_mon; eauto. i. pclearbot. auto. }
  Qed.

  Record simulation: Prop := mk_simulation {
    sim_init: exists i_src0 i_tgt0, <<SIM: sim i_src0 i_tgt0 L0.(initial_state) L1.(initial_state)>>;
  }
  .

  Lemma admitt: False. Admitted.
  Ltac admitt := exfalso; apply admitt.

  Ltac pc H := rr in H; desH H; ss.
  Lemma adequacy_spin
        i_src0 i_tgt0 st_src0 st_tgt0
        (SIM: sim i_src0 i_tgt0 st_src0 st_tgt0)
        (SPIN: Beh.state_spin L1 st_tgt0)
    :
      <<SPIN: Beh.state_spin L0 st_src0>>
  .
  Proof.
    ginit.
    { i. eapply cpn1_wcompat; eauto. eapply Beh.state_spin_mon. }
    revert i_src0 i_tgt0 st_src0 st_tgt0 SIM SPIN. gcofix CIH.
    intros ? ? ? ? SIM. induction SIM using sim_ind; i; clarify.
    - (** final **)
      exfalso. punfold SPIN. inv SPIN; rewrite SRT0 in *; ss.
    - (** dsrc **)
      des. gstep. econs 2; eauto. esplits; eauto.
      eapply gpaco1_mon; eauto. ss.
    - (** dtgt **)
      punfold SPIN. inv SPIN; rewrite SRT in *; ss. des. pclearbot.
      exploit wf_demonic; et; i; clarify.
      exploit SIM; et. i; des. eapply IH; eauto.
    - (** progress **)
      remember false in SIM at 1.
      remember false in SIM at 1.
      revert Heqb. clear Heqb0. revert SPIN.
      induction SIM using sim_ind; i; clarify.
      + exfalso. punfold SPIN. inv SPIN; rewrite SRT1 in *; clarify.
      + des. gstep. econs 2; auto. esplits; eauto.
        gbase. eapply CIH; eauto.
      + punfold SPIN. inv SPIN; rewrite SRT in *; clarify. des.
        exploit wf_demonic; et; i; clarify. pclearbot.
        exploit SIM; et. i; des. eapply IH; eauto.
  Qed.

  Lemma adequacy_aux
        i_src0 i_tgt0 st_src0 st_tgt0
        (SIM: sim i_src0 i_tgt0 st_src0 st_tgt0)
    :
      <<IMPR: Beh.improves (Beh.of_state L0 st_src0) (Beh.of_state L1 st_tgt0)>>
  .
  Proof.
    ginit.
    { i. eapply cpn2_wcompat; eauto. eapply Beh.of_state_mon. }
    revert i_tgt0 i_src0 st_src0 st_tgt0 SIM. gcofix CIH.
    i. rename x2 into tr.
    punfold PR. revert i_src0 i_tgt0 st_src0 SIM.
    induction PR using Beh.of_state_ind; ii; ss; rename st0 into st_tgt0.
    - (** done **)
      revert retv H.
      induction SIM using sim_ind; i; clarify.
      + rewrite SRT0 in *. clarify. gstep. econs; eauto.
      + des. guclo indC_spec. econs 5; eauto. red. esplits; eauto.
      + rewrite SRT in *. clarify.
      + admitt.
    - (** spin **)
      exploit adequacy_spin; eauto. i.
      gstep. econs. et.
    - (** nb **)
      gstep. econs; eauto.
    - (** cons **)
      pc TL. induction SIM using sim_ind; i; try rewrite SRT in *; clarify.
      + (** d_ **)
        des. guclo indC_spec. econs 5; eauto. red. esplits; eauto.
      + (** progress **)
        remember false in SIM at 1.
        remember false in SIM at 1.
        clear Heqb0. revert Heqb.
        revert ev SRT STEP.
        induction SIM using sim_ind; i; try rewrite SRT0 in *; clarify.
        * des. guclo indC_spec. econs 5; eauto. red. esplits; eauto.

          exploit IH; eauto. i.
          guclo indC_spec. econs 5; eauto. red. esplits; eauto.
        *


          rewrite SRT0 in *. clarify.
        * rewrite SRT0 in *. clarify.
        * rewrite SRT0 in *. clarify.


        punfold SIM. induction SIM with

                       inv SIM; try rewrite SRT in *; clarify.
        des.


        eapply IH; eauto.
        guclo Beh.dstep_clo_spec. econs; eauto.
      + (** a_ **)
        guclo Beh.astep_clo_spec. econs; eauto. ii.
        exploit SIM0; et. i. des. pc SIM. et.

      revert i_src0 st_src0 SIM.
      induction (WFTGT i_tgt0).
      clear H. rename x into i_tgt0. rename H0 into IHTGT. i.
      pc TL. punfold SIM. inv SIM; try rewrite SRT in *; ss.
      + (** vv **)
        specialize (SIM0 ev st1). apply SIM0 in STEP; clear SIM0; des.
        gstep. econs 4; eauto. pc SIM. gbase. eapply CIH; eauto.
      + (** vis stuck **)
        apply STUCK in STEP. clarify.
      + (** d_ **)
        des. pc SIM.
        guclo Beh.dstep_clo_spec. econs; eauto.
      + (** a_ **)
        guclo Beh.astep_clo_spec. econs; eauto. ii.
        exploit SIM0; et. i. des. pc SIM. et.
    - (** demonic **)
      revert i_src0 st_src0 SIM.
      induction (WFTGT i_tgt0).
      clear H. rename x into i_tgt0. rename H0 into IHTGT. i.
      rr in STEP. des. clarify. rename st1 into st_tgt1.
      punfold SIM. inv SIM; try rewrite SRT in *; ss.
      + des. pc SIM.
        guclo Beh.dstep_clo_spec. econs; et.
      + exploit SIM0; et. i. des. pc SIM.
        eapply IH; et.
      + guclo Beh.astep_clo_spec. econs; et. ii.
        exploit SIM0; et. i. des. pc SIM. et.
    - (** angelic **)
      revert i_src0 st_src0 SIM.
      induction (WFTGT i_tgt0).
      clear H. rename x into i_tgt0. rename H0 into IHTGT. i.
      punfold SIM. inv SIM; try rewrite SRT in *; ss.
      + des. pc SIM.
        guclo Beh.dstep_clo_spec. econs; et.
      + guclo Beh.astep_clo_spec. econs; et. ii.
        exploit SIM0; et. i. des. pc SIM. et.
      + des. pc SIM. exploit STEP; et. i. des. et.
  Qed.

  Theorem adequacy
          (SIM: simulation)
    :
      <<IMPR: Beh.improves (Beh.of_program L0) (Beh.of_program L1)>>
  .
  Proof.
    inv SIM. des.
    eapply adequacy_aux; et.
  Qed.

End SIM.
Hint Constructors _sim.
Hint Unfold sim.
Hint Resolve sim_mon: paco.
