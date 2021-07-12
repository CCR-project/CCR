Require Import Coqlib.
Require Import STS.
Require Import Behavior.

Set Implicit Arguments.

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
  Variable idx_src: Type.
  Variable idx_tgt: Type.
  Variable ord_src: idx_src -> idx_src -> Prop.
  Variable ord_tgt: idx_tgt -> idx_tgt -> Prop.

  Hypothesis ORDSRCTRANS: Transitive ord_src.

  Variant _sim sim (i_src0: idx_src) (i_tgt0: idx_tgt) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | sim_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0

  | sim_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: exists i_src1 i_tgt1, sim i_src1 i_tgt1 st_src1 st_tgt1>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0

  | sim_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0

  | sim_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (* (FIN: _.(state_sort) st_src0 = final <-> _.(state_sort) st_tgt0 = final) *)
      (SIM: exists st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          exists i_src1 i_tgt1, <<ORD: ord_tgt i_tgt1 i_tgt0>> /\ <<SIM: sim i_src1 i_tgt1 st_src1 st_tgt0>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0
  | sim_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (* (FIN: _.(state_sort) st_src0 = final <-> _.(state_sort) st_tgt0 = final) *)
      (SIM: forall st_tgt1
          (STEP: _.(step) st_tgt0 None st_tgt1)
        ,
          exists i_src1 i_tgt1, <<ORD: ord_src i_src1 i_src0>> /\ <<SIM: sim i_src1 i_tgt1 st_src0 st_tgt1>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0
  | sim_angelic_src
      (SRT: _.(state_sort) st_src0 = angelic)
      (* (FIN: _.(state_sort) st_src0 = final <-> _.(state_sort) st_tgt0 = final) *)
      (SIM: forall st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          exists i_src1 i_tgt1, <<ORD: ord_tgt i_tgt1 i_tgt0>> /\ <<SIM: sim i_src1 i_tgt1 st_src1 st_tgt0>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0
  | sim_angelic_tgt
      (SRT: _.(state_sort) st_tgt0 = angelic)
      (* (FIN: _.(state_sort) st_src0 = final <-> _.(state_sort) st_tgt0 = final) *)
      (SIM: exists st_tgt1
          (STEP: _.(step) st_tgt0 None st_tgt1)
        ,
          exists i_src1 i_tgt1, <<ORD: ord_src i_src1 i_src0>> /\ <<SIM: sim i_src1 i_tgt1 st_src0 st_tgt1>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0
  .

  Definition sim: _ -> _ -> _ -> _ -> Prop := paco4 _sim bot4.

  Lemma sim_mon: monotone4 _sim.
  Proof.
    ii. inv IN.
    - econs 1; et.
    - econs 2; et. i. exploit SIM; et. i; des. esplits; et.
    - econs 3; et.
    - econs 4; et. des. esplits; et.
    - econs 5; et. i. exploit SIM; et. i; des. esplits; et.
    - econs 6; et. i. exploit SIM; et. i; des. esplits; et.
    - econs 7; et. des. esplits; et.
  Qed.

  Hint Constructors _sim.
  Hint Unfold sim.
  Hint Resolve sim_mon: paco.

  Record simulation: Prop := mk_simulation {
    sim_wf_ord_src: <<WF: well_founded ord_src>>;
    sim_wf_ord_tgt: <<WF: well_founded ord_tgt>>;
    sim_init: exists i_src0 i_tgt0, <<SIM: sim i_src0 i_tgt0 L0.(initial_state) L1.(initial_state)>>;
  }
  .

  Hypothesis WFSRC: well_founded ord_src.
  Hypothesis WFTGT: well_founded ord_tgt.

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
    intros i_src0. induction (WFSRC i_src0).
    clear H. rename x into i_src0. rename H0 into IH. i.
    punfold SIM. inv SIM.
    - (** final **)
      des. exfalso. punfold SPIN. inv SPIN; rewrite SRT1 in *; ss.
    - (** vis **)
      des. exfalso. punfold SPIN. inv SPIN; rewrite SRT1 in *; ss.
    - (** vis stuck **)
      exfalso. punfold SPIN. inv SPIN; rewrite SRT0 in *; ss.
    - (** dsrc **)
      des. pc SIM. gstep. econs 2; et. esplits; et. gbase. et.
    - (** dtgt **)
      punfold SPIN. inv SPIN; try rewrite SRT in *; ss. des; clarify.
      pc TL. exploit wf_demonic; et; i; clarify.
      exploit SIM0; et. i; des. pc SIM. eapply IH; et.
    - (** asrc **)
      punfold SPIN. inv SPIN; ss.
      + gstep. econs 1; et. ii.
        exploit L0.(wf_angelic); et. i; clarify. esplits; et.
        exploit SIM0; et. i; des. pc SIM.
        gbase. eapply CIH; et.
      + des; clarify. rename st1 into st_tgt1.
        exploit wf_demonic; et; i; clarify.
        gstep. econs; et. ii. exploit wf_angelic; et; i; clarify.
        pc TL. exploit SIM0; et. i; des. pc SIM.
        gbase. eapply CIH; et. pfold. econs 2; et. esplits; et.
    - (** atgt **)
      des. pc SIM. eapply IH; eauto. eapply spin_astep; et.
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
      revert i_src0 st_src0 SIM.
      induction (WFTGT i_tgt0).
      clear H0. rename x into i_tgt0. rename H1 into IHTGT. i.
      punfold SIM. inv SIM; try rewrite H in *; ss.
      + (** ff **)
        gstep. econs; eauto. clarify.
      + (** d_ **)
        des. pc SIM.
        guclo Beh.dstep_clo_spec. econs; et.
      + (** a_ **)
        guclo Beh.astep_clo_spec. econs; et.
        i. exploit SIM0; et. i. des. pc SIM. et.
    - (** spin **)
      exploit adequacy_spin; eauto. i.
      gstep. econs. et.
    - (** nb **)
      gstep. econs; eauto.
    - (** cons **)
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
