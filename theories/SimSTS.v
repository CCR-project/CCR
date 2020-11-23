Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.

Set Implicit Arguments.

(* Definition option_to_list X (ox: option X): list X := match ox with | Some x => [x] | _ => [] end. *)
(* Coercion option_to_list_coercion := option_to_list. *)

(* Definition PStep L (P: L.(state) -> Prop) (st0: L.(state)) (ev: option event) (st1: (L.(state))): Prop := *)
(*   (<<PROP: P st0>>) /\ (<<STEP: L.(step) st0 ev st1>>) *)
(* . *)

(* Inductive PStar L (P: L.(state) -> Prop) (st0: L.(state)): (list event) -> (L.(state)) -> Prop := *)
(* | star_refl *)
(*     (PROP: P st0) *)
(*     (* ev_sum *) *)
(*     (* (EV: ev_sum = []) *) *)
(*   : *)
(*     PStar L P st0 [] st0 *)
(* | star_step *)
(*     ev evs st1 st2 *)
(*     (STEP: PStep L P st0 ev st1) *)
(*     (STAR: PStar L P st1 evs st2) *)
(*     (* ev_sum *) *)
(*     (* (EV: ev_sum = ev ++ evs) *) *)
(*   : *)
(*     PStar L P st0 (ev ++ evs) st2 *)
(* . *)

(* Inductive PPlus L (P: L.(state) -> Prop) (st0: L.(state)): (list event) -> (L.(state)) -> Prop := *)
(* | plus_intro *)
(*     ev evs st1 st2 *)
(*     (STEP: PStep L P st0 ev st1) *)
(*     (STAR: PStar L P st1 evs st2) *)
(*   : *)
(*     PPlus L P st0 (ev ++ evs) st2 *)
(* . *)

(* Definition DStep L (st0: (L.(state))) (ev: option event) (st1: L.(state)) := *)
(*   PStep L (fun st => L.(state_sort) st = demonic) st0 ev st1. *)
(* Definition AStep L (st0: (L.(state))) (ev: option event) (st1: L.(state)) := *)
(*   PStep L (fun st => L.(state_sort) st = angelic) st0 ev st1. *)
(* Definition DPlus L (st0: (L.(state))) (evs: list event) (st1: L.(state)) := *)
(*   PPlus L (fun st => L.(state_sort) st = demonic) st0 evs st1. *)
(* Definition APlus L (st0: (L.(state))) (evs: list event) (st1: L.(state)) := *)
(*   PPlus L (fun st => L.(state_sort) st = angelic) st0 evs st1. *)
(* Hint Unfold DStep AStep. *)
(* Hint Unfold DPlus APlus. *)

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

(* Lemma spin_noevent *)
(*       L st0 e st1 *)
(*       (STAR: PStar L (fun st => _.(state_sort) st = angelic) st0 [e] st1) *)
(*       (SPIN: Beh.state_spin _ st0) *)
(*   : *)
(*     False *)
(* . *)
(* Proof. *)
(*   remember [e] as tmp in STAR. revert Heqtmp. *)
(*   induction STAR; ii; ss. punfold SPIN. rr in STEP; des. inv SPIN; ii; rewrite PROP in *; ss. *)
(*   destruct ev, evs; ss; clarify. *)
(*   - exploit wf_angelic; et. i; ss. *)
(*   - exploit STEP; eauto. i; des; ss. pclearbot. eapply IHSTAR; eauto. *)
(* Qed. *)

(* Lemma spin_astar *)
(*       L st0 st1 *)
(*       (STAR: PStar L (fun st => _.(state_sort) st = angelic) st0 [] st1) *)
(*       (SPIN: Beh.state_spin _ st0) *)
(*   : *)
(*     <<SPIN: Beh.state_spin _ st1>> *)
(* . *)
(* Proof. *)
(*   remember [] as tmp in STAR. revert Heqtmp. *)
(*   revert SPIN. induction STAR; ii; ss. *)
(*   { destruct ev, evs; ss. dup SPIN. rr in STEP; des. punfold SPIN. inv SPIN; rewrite PROP in *; ss. *)
(*     exploit STEP; eauto. i; des. pclearbot. eapply IHSTAR; ss. } *)
(* Qed. *)

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
  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.

  Variant _sim sim (i0: idx) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | sim_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _sim sim i0 st_src0 st_tgt0

  | sim_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      i1 ev st_src1 st_tgt1
      (STEP: _.(step) st_src0 (Some ev) st_src1)
      (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
      (SIM: (sim i1 st_src1 st_tgt1): Prop)
    :
      _sim sim i0 st_src0 st_tgt0


  | sim_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (* (FIN: _.(state_sort) st_src0 = final <-> _.(state_sort) st_tgt0 = final) *)
      (SIM: exists st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src1 st_tgt0>>)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (* (FIN: _.(state_sort) st_src0 = final <-> _.(state_sort) st_tgt0 = final) *)
      (SIM: forall st_tgt1
          (STEP: _.(step) st_tgt0 None st_tgt1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src0 st_tgt1>>)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_angelic_src
      (SRT: _.(state_sort) st_src0 = angelic)
      (* (FIN: _.(state_sort) st_src0 = final <-> _.(state_sort) st_tgt0 = final) *)
      (SIM: forall st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src1 st_tgt0>>)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_angelic_tgt
      (SRT: _.(state_sort) st_tgt0 = angelic)
      (* (FIN: _.(state_sort) st_src0 = final <-> _.(state_sort) st_tgt0 = final) *)
      (SIM: exists st_tgt1
          (STEP: _.(step) st_tgt0 None st_tgt1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src0 st_tgt1>>)
    :
      _sim sim i0 st_src0 st_tgt0


  | sim_demonic_both
      (SRT: _.(state_sort) st_src0 = demonic)
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
          (STEP: _.(step) st_tgt0 None st_tgt1)
        ,
          exists st_src1 (STEP: _.(step) st_src0 None st_src1),
            <<SIM: exists i1, sim i1 st_src1 st_tgt1>>)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_angelic_both
      (SRT: _.(state_sort) st_src0 = angelic)
      (SRT: _.(state_sort) st_tgt0 = angelic)
      (SIM: forall st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          exists st_tgt1 (STEP: _.(step) st_tgt0 None st_tgt1),
            <<SIM: exists i1, sim i1 st_src1 st_tgt1>>)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_demonic_angelic
      (SRT: _.(state_sort) st_src0 = demonic)
      (SRT: _.(state_sort) st_tgt0 = angelic)
      (SIM: exists st_tgt1
          (STEP: _.(step) st_tgt0 None st_tgt1)
        ,
          exists st_src1 (STEP: _.(step) st_src0 None st_src1),
            <<SIM: exists i1, sim i1 st_src1 st_tgt1>>)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_angelic_demonic
      (SRT: _.(state_sort) st_src0 = angelic)
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          forall st_tgt1 (STEP: _.(step) st_tgt0 None st_tgt1),
            <<SIM: exists i1, sim i1 st_src1 st_tgt1>>)
    :
      _sim sim i0 st_src0 st_tgt0
  .

  Definition sim: _ -> _ -> _ -> Prop := paco3 _sim bot3.

  Lemma sim_mon: monotone3 _sim.
  Proof.
    ii. inv IN.

    - econs 1; et.
    - econs 2; et.
    - econs 3; et. des. esplits; et.
    - econs 4; et. i. exploit SIM; et. i; des. esplits; et.
    - econs 5; et. i. exploit SIM; et. i; des. esplits; et.
    - econs 6; et. des. esplits; et.
    - econs 7; et. i. exploit SIM; et. i; des. esplits; et.
    - econs 8; et. i. exploit SIM; et. i; des. esplits; et.
    - econs 9; et. des. esplits; et.
    - econs 10; et. i. exploit SIM; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim.
  Hint Unfold sim.
  Hint Resolve sim_mon: paco.

  Record simulation: Prop := mk_simulation {
    sim_wf_ord: <<WF: well_founded ord>>;
    sim_init: exists i0, <<SIM: sim i0 L0.(initial_state) L1.(initial_state)>>;
  }
  .

  Hypothesis WF: well_founded ord.

  Ltac pc H := rr in H; desH H; ss.
  Lemma adequacy_spin
        i0 st_src0 st_tgt0
        (SIM: sim i0 st_src0 st_tgt0)
        (SPIN: Beh.state_spin L1 st_tgt0)
    :
      <<SPIN: Beh.state_spin L0 st_src0>>
  .
  Proof.
    revert_until WF.
    ginit.
    { i. eapply cpn1_wcompat; eauto. eapply Beh.state_spin_mon. }
    gcofix CIH. i.
    revert_until i0. pattern i0. eapply well_founded_ind; eauto. clear i0. i.
    rename x into i0. rename H into IH.

    punfold SIM. inv SIM.
    - (** final **)
      des. exfalso. punfold SPIN. inv SPIN; rewrite SRT1 in *; ss.
    - (** vis **)
      des. exfalso. punfold SPIN. inv SPIN; rewrite SRT1 in *; ss.
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
        gbase. eapply CIH; eauto.
      + des; clarify. rename st1 into st_tgt1.
        exploit wf_demonic; et; i; clarify.
        gstep. econs; et. ii. exploit wf_angelic; et; i; clarify.
        pc TL. exploit SIM0; et. i; des. pc SIM.
        (* gbase. eapply CIH; et. pfold; econs 2; et. esplits; et. *)
        eapply gpaco1_mon. { eapply IH; et. pfold; econs 2; et. esplits; et. } { ss. } { ss. }
    - (** atgt **)
      des. pc SIM. eapply IH; eauto. eapply spin_astep; et.
    - (** dd **)
      punfold SPIN. inv SPIN; rewrite SRT0 in *; ss. des.
      exploit wf_demonic; et; i; clarify. pc TL.
      exploit SIM0; et. i; des. pc SIM.
      gstep. econs 2; et. esplits; et. gbase. eapply CIH; et.
    - (** aa **)
      punfold SPIN. inv SPIN; rewrite SRT0 in *; ss. des.
      gstep. econs; et. ii.
      exploit L0.(wf_angelic); et; i; clarify.
      exploit SIM0; et. i; des. pc SIM.
      gbase. eapply CIH; et. eapply spin_astep; et.
    - (** da **)
      des. pc SIM. gstep. econs 2; et. esplits; et. gbase. eapply CIH; et. eapply spin_astep; et.
    - (** ad **)
      gstep. econs 1; et. ii.
      exploit L0.(wf_angelic); et; i; clarify.
      punfold SPIN. inv SPIN; rewrite SRT0 in *; ss. des; clarify. pc TL.
      exploit (wf_demonic); et; i; clarify.
      exploit SIM0; et. i; des. pc x.
      gbase. eapply CIH; et.
  Qed.

  Lemma adequacy_aux
        i0 st_src0 st_tgt0
        (SIM: sim i0 st_src0 st_tgt0)
    :
      <<IMPR: Beh.improves (Beh.of_state L0 st_src0) (Beh.of_state L1 st_tgt0)>>
  .
  Proof.
    revert_until WF.
    (* ginit. *)
    (* { i. eapply cpn2_wcompat; eauto. eapply Beh.of_state_mon. } *)
    (* gcofix CIH. i. *)
    pcofix CIH. i.
    rename x2 into tr.
    punfold PR. generalize dependent st_src0. generalize dependent i0.
    induction PR using Beh.of_state_ind; ii; ss; rename st0 into st_tgt0.
    - (** done **)
      move i0 before CIH. revert_until i0. pattern i0.
      eapply well_founded_ind; eauto. clear i0. i.
      rename x into i0. rename H into IH.

      punfold SIM. inv SIM; try rewrite H0 in *; ss.
      + (** ff **)
        pfold. econs; eauto. clarify.
      + (** d_ **)
        des. pc SIM.
        pfold. econs 5; eauto. rr. esplits; eauto.
        exploit IH; eauto. intro A. punfold A.
      + (** a_ **)
        pfold. econs 6; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        esplits; eauto.
        exploit SIM0; eauto. i; des. pc SIM.
        exploit IH; eauto. intro A. punfold A.
    - (** spin **)
      exploit adequacy_spin; eauto.
    - (** nb **)
      pfold. econs; eauto.
    - (** cons **)
      move i0 before CIH. revert_until i0. pattern i0.
      eapply well_founded_ind; eauto. clear i0. i.
      rename x into i0. rename H into IH.

      pc TL.
      punfold SIM. inv SIM; try rewrite SRT in *; ss.
      + (** vv **)
        exploit wf_vis. { eapply SRT. } { eauto. } { eapply STEP. } i; des; clarify.
        pfold. econs 4; eauto. pc SIM0. right. eapply CIH; eauto.
      + (** d_ **)
        des. pc SIM.
        pfold. econs 5; eauto. rr. esplits; eauto.
        exploit IH; et. intro A. punfold A.
      + (** a_ **)
        pfold. econs 6; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i; des. pc SIM.
        esplits; eauto.
        exploit IH; et. intro A. punfold A.
    - (** demonic **)
      rr in STEP. des. clarify. rename st1 into st_tgt1.
      move i0 before CIH. move IH before i0. move SRT before i0. revert_until TL.
      pattern i0.
      eapply well_founded_ind; eauto. clear i0. i.
      rename x into i0. rename H into IHi.
      punfold SIM. inv SIM; try rewrite SRT in *; ss.
      + (** d_ **)
        des. pc SIM.
        pfold. econs 5; eauto. rr. esplits; eauto.
        exploit IHi; et. intro A. punfold A.
      + (** _d **)
        exploit SIM0; eauto. i; des. pc SIM. exploit IH; et.
      + (** a_ **)
        pfold. econs 6; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i; des. pc SIM.
        esplits; eauto.
        exploit IHi. { et. } { et. } intro A. punfold A.
      + (** dd **)
        exploit SIM0; et. i; des. pc SIM.
        exploit IH; et. intro A.
        eapply Beh._beh_dstep; et.
      + (** ad **)
        pfold. econs 6; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; et. i; des. pc x.
        esplits; eauto.
        exploit IH; et. intro A.
        punfold A.

    - (** angelic **)
      move i0 before CIH. move STEP before i0. move SRT before i0. revert_until STEP.
      pattern i0.
      eapply well_founded_ind; eauto. clear i0. i.
      rename x into i0. rename H into IHi.
      punfold SIM. inv SIM; try rewrite SRT in *; ss.
      + (** d_ **)
        des. pc SIM.
        pfold. econs 5; eauto. rr. esplits; eauto.
        exploit IHi; et. intro A. punfold A.
      + (** a_ **)
        pfold. econs 6; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i; des. pc SIM.
        esplits; eauto.
        exploit IHi; et. intro A. punfold A.
      + (** _a **)
        des. pc SIM. exploit STEP; et. i; des.
        exploit IH; et.
      + (** aa **)
        pfold. econs 6; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i; des. pc SIM.
        esplits; eauto.
        exploit STEP; et. i; des.
        exploit IH; et. intro A. punfold A.
      + (** da **)
        des. pc SIM.
        exploit STEP; et. i; des.
        exploit IH. { et. } intro A.
        eapply Beh._beh_dstep; et.
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
