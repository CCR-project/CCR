Require Import sflib.
Require Import Universe.
Require Import Semantics.
Require Import Behavior.
From Paco Require Import paco.
Require Import RelationClasses List.
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.

Set Implicit Arguments.

Definition single X (x: X): X -> Prop := fun x0 => x = x0.



(* Section SSET. *)
(*   Context `{L: semantics}. *)
(*   Record elem: Type := mk_elem { elem_st:> L.(state) ; guarded:> bool ; accum:> list syscall }. *)
(*   Definition sset: Type := ((elem -> Prop) -> Prop). *)
(* End SSET. *)

(* Section SIM. *)

(* Variable L0 L1: semantics. *)

(* Inductive _sim (sim: @sset L0 -> @sset L1 -> Prop): _ -> _ -> Prop := *)
(* (* | sim_expand *) *)
(* | sim_pointwise *)
(*     sss_src0 sss_tgt0 *)
(*     (SIM: sim sss_src0 sss_tgt0) *)
(*     (POINT: forall ss_tgt0 (IN: sss_tgt0 ss_tgt0), *)
(*         exists ss_src0, (<<IN: sss_src0 ss_src0>>) /\ *)
(*                         (<<SIM: forall s_src0 (IN: ss_src0 s_src0), *)
(*                             exists s_tgt0, (<<IN: ss_tgt0 s_tgt0>>) /\ *)
(*                                            (<<SIM: sim (single (single s_src0)) (single (single s_tgt0))>>) *)
(*                                              >>)) *)
(*   : *)
(*     _sim sim sss_src0 sss_tgt0 *)
(* . *)

Lemma spin_nofinal
      L st0
      (SPIN: Beh.state_spin L st0)
  :
    <<NOFIN: L.(state_sort) st0 <> final>>
.
Proof.
  punfold SPIN. inv SPIN; ii; rewrite H in *; ss.
Qed.

Section SIM.

  Variable L0 L1: semantics.
  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.

  Variant _sim sim (i0: idx) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | sim_final
      (FINTGT: L1.(state_sort) st_tgt0 = final)
      (FINSRC: L0.(state_sort) st_src0 = final)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_demonic_tgt
      (DEM: L1.(state_sort) st_tgt0 = demonic)
      (DEMTGT: forall
          st_tgt1
          (STEPTGT: L1.(step) st_tgt0 None st_tgt1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src0 st_tgt1>>)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_demonic_src
      (DEM: L0.(state_sort) st_src0 = demonic)
      (DEMSRC: exists
          st_src1
          (STEPSRC: L0.(step) st_src0 None st_src1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src1 st_tgt0>>)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_demonic_both
      (DEM: L0.(state_sort) st_src0 = demonic)
      (DEM: L1.(state_sort) st_tgt0 = demonic)
      (DEMTGT: forall
          ev st_tgt1
          (STEPTGT: L1.(step) st_tgt0 ev st_tgt1)
        ,
          exists i1 st_src1, <<ORD: ord i1 i0>> /\ <<STEP: L0.(step) st_src0 ev st_src1>> /\
                                                           <<SIM: sim i1 st_src0 st_tgt0>>)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_angelic_src
      (ANG: L0.(state_sort) st_src0 = angelic)
      (ANGSRC: forall
          st_src1
          (STEPSRC: L0.(step) st_src0 None st_src1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src1 st_tgt0>>)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_angelic_tgt
      (ANG: L1.(state_sort) st_tgt0 = angelic)
      (ANGTGT: exists
          st_tgt1
          (STEPTGT: L1.(step) st_tgt0 None st_tgt1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src0 st_tgt1>>)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_angelic_both
      (ANG: L0.(state_sort) st_src0 = angelic)
      (ANG: L1.(state_sort) st_tgt0 = angelic)
      (ANGSRC: forall
          ev st_src1
          (STEPSRC: L0.(step) st_src0 ev st_src1)
        ,
          exists i1 st_tgt1, <<ORD: ord i1 i0>> /\ <<STEP: L1.(step) st_tgt0 ev st_tgt1>> /\
                                                           <<SIM: sim i1 st_src0 st_tgt0>>)
    :
      _sim sim i0 st_src0 st_tgt0
  .

  Definition sim: _ -> _ -> _ -> Prop := paco3 _sim bot3.

  Lemma sim_mon: monotone3 _sim.
  Proof.
    ii. inv IN; try (by econs; eauto).

    - econs 2; et. ii. exploit DEMTGT; et. i; des; et.
    - econs 3; et. des. esplits; eauto.
    - econs 4; et. ii. exploit DEMTGT; et. i; des; et. esplits; et.

    - econs 5; et. ii. exploit ANGSRC; et. i; des; et.
    - econs 6; et. des. esplits; eauto.
    - econs 7; et. ii. exploit ANGSRC; et. i; des; et. esplits; et.
  Qed.

  Hint Constructors _sim.
  Hint Unfold sim.
  Hint Resolve sim_mon: paco.

  Record simulation: Prop := mk_simulation {
    sim_wf_ord: <<WF: well_founded ord>>;
    sim_init: exists i0, <<SIM: sim i0 L0.(initial_state) L1.(initial_state)>>;
  }
  .

  Lemma adequacy_aux
        (WF: well_founded ord)
        i0 st_src0 st_tgt0
        (SIM: sim i0 st_src0 st_tgt0)
    :
      <<IMPR: Beh.improves (Beh.of_state L0 st_src0) (Beh.of_state L1 st_tgt0)>>
  .
  Proof.
    revert_until WF.
    ginit.
    { i. eapply cpn2_wcompat; eauto. eapply Beh.of_state_mon. }
    gcofix CIH. i.
    revert_until i0. pattern i0. eapply well_founded_ind; eauto. clear i0. i.
    rename x into i0. rename H into IH. rename x2 into tr.

    punfold SIM. inv SIM.
    - gstep. punfold PR. inv PR; ss; try rewrite FINTGT in *; clarify.
      + (** fin **) econs; ss; et.
      + (** spin **) eapply spin_nofinal in SPIN; ss.
    - punfold PR.
      Require Import Program.

      inv PR; ss; try rewrite DEM in *; clarify.
      + (** spin **)
        punfold SPIN. inv SPIN; try rewrite DEM in *; ss. des. clarify. pclearbot.
        rename st1 into st_tgt1.
        exploit DEMTGT; eauto. i; des. r in SIM; des; ss.
        exploit IH; eauto.
      + (** nb **) gstep; econs; eauto.
      + (** dem tau **)
        rr in STEP. des. clarify.
        exploit DEMTGT; et. i; des. r in SIM; des; ss. eapply IH; eauto.
      + (** dem sys **)
        rr in STEP. des. clarify. r in TL; des; ss.
        exploit DEMTGT; et. i; des. r in SIM; des; ss.
        rename st1 into st_tgt1.

        gstep.
        pfold.
        (*** st_tgt0 --ev--> st_tgt1 ---> evs
             st_src0
         ***)
        eapply IH; eauto. pfold. econs; eauto.
        pfold. econs 6; eauto. eapply IH; eauto.


      clear DEM.
      dependent induction PR using Beh.of_state_ind; ss; try rewrite DEM in *; clarify;
        rename st0 into st_tgt0.
      + (** spin **)
        rename H into SPIN.
        punfold SPIN. inv SPIN; try rewrite DEM in *; ss. des. clarify. pclearbot.
        rename st1 into st_tgt1.
        exploit DEMTGT; eauto. i; des. revert TL. pclearbot. i.
        exploit IH; eauto.
      + (** nb **) pfold; econs; eauto.
      + (** dem tau **)
        rr in STEP. des. clarify. exploit DEMTGT; eauto. i; des. Fail progress pclearbot.
        r in SIM; des; ss.
        rename st1 into st_tgt1.
        eapply IH0.
      + (** **)




      dependent induction PR using Beh.of_state_ind; ss; try rewrite DEM in *; clarify;
        rename st0 into st_tgt0.
      + (** spin **)
        rename H into SPIN.
        punfold SPIN. inv SPIN; try rewrite DEM in *; ss. des. clarify. pclearbot.
        rename st1 into st_tgt1.
        exploit DEMTGT; eauto. i; des. revert TL. pclearbot. i.
        exploit IH; eauto.
      + (** nb **) pfold; econs; eauto.
      + (** dem tau **)
        rr in STEP. des. clarify. exploit DEMTGT; eauto. i; des. Fail progress pclearbot.
        r in SIM; des; ss.
        rename st1 into st_tgt1.
        eapply IH0.
      + (** **)
  Qed.

  Theorem adequacy
          (SIM: simulation)
    :
      <<IMPR: Beh.improves (Beh.of_program L0) (Beh.of_program L1)>>
  .
  Proof.
    pcofix CIH. i.
  Qed.

End SIM.
Hint Constructors _sim.
Hint Unfold sim.
Hint Resolve sim_mon: paco.

Theorem adequacy
        L0 L1
Theorem compsim_compat
  :
    Beh.improves (Beh.of_program L0) (Beh.of_program L1)
.
Proof.
  unfold Beh.of_program.
  r.
  ginit.
  { i. eapply cpn2_wcompat; eauto. eapply Beh.of_state_mon. }
  gcofix CIH. i. rename x2 into tr.
  - guclo Simple.bsim_spec.
    econs; eauto.
    r. des_ifs.
    ii.
    apply gpaco2_gupaco; eauto.
    { eapply Beh.of_state_mon. }
    eapply Simple.bsim_compat.

    guclo Simple.bsim_compat. gclo. Set Printing All. Compute (fun _ : state L0 => Tr.t).
Qed.

End SIM.
