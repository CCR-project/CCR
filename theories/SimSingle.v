Require Import sflib.
Require Import Universe.
Require Import Semantics.
Require Import Behavior.
From Paco Require Import paco.
Require Import RelationClasses List.
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.
Require Import String.

Set Implicit Arguments.

Definition single X (x: X): X -> Prop := fun x0 => x = x0.

Ltac determ_tac LEMMA :=
  let tac := eauto in
  let x := rev_all ltac:(fun f => apply f) in
  let y := all ltac:(fun f => apply f) in
  first[
      exploit LEMMA; [x|y|]
    | exploit LEMMA; [tac|x|y|]
    | exploit LEMMA; [tac|tac|x|y|]
    | exploit LEMMA; [tac|tac|tac|x|y|]
    | exploit LEMMA; [tac|tac|tac|tac|x|y|]
    ];
  i; des; clarify.



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

Definition is_some X (ox: option X): bool := match ox with | Some x => true | _ => false end.

Definition option_to_list X (ox: option X): list X := match ox with | Some x => [x] | _ => [] end.
Coercion option_to_list_coercion := option_to_list.

Definition PStep L (P: L.(state) -> Prop) (st0: L.(state)) (ev: option event) (st1: (L.(state))): Prop :=
  (<<PROP: P st0>>) /\ (<<STEP: L.(step) st0 ev st1>>)
.

Inductive PStar L (P: L.(state) -> Prop) (st0: L.(state)): (list event) -> (L.(state)) -> Prop :=
| star_refl
    (PROP: P st0)
    (* ev_sum *)
    (* (EV: ev_sum = []) *)
  :
    PStar L P st0 [] st0
| star_step
    ev evs st1 st2
    (STEP: PStep L P st0 ev st1)
    (STAR: PStar L P st1 evs st2)
    (* ev_sum *)
    (* (EV: ev_sum = ev ++ evs) *)
  :
    PStar L P st0 (ev ++ evs) st2
.

Inductive PPlus L (P: L.(state) -> Prop) (st0: L.(state)): (list event) -> (L.(state)) -> Prop :=
| plus_intro
    ev evs st1 st2
    (STEP: PStep L P st0 ev st1)
    (STAR: PStar L P st1 evs st2)
  :
    PPlus L P st0 (ev ++ evs) st2
.

Definition DStep L (st0: (L.(state))) (ev: option event) (st1: L.(state)) :=
  PStep L (fun st => L.(state_sort) st = demonic) st0 ev st1.
Definition AStep L (st0: (L.(state))) (ev: option event) (st1: L.(state)) :=
  PStep L (fun st => L.(state_sort) st = angelic) st0 ev st1.
Definition DPlus L (st0: (L.(state))) (evs: list event) (st1: L.(state)) :=
  PPlus L (fun st => L.(state_sort) st = demonic) st0 evs st1.
Definition APlus L (st0: (L.(state))) (evs: list event) (st1: L.(state)) :=
  PPlus L (fun st => L.(state_sort) st = angelic) st0 evs st1.
Hint Unfold DStep AStep.
Hint Unfold DPlus APlus.

Lemma spin_nofinal
      L st0
      (SPIN: Beh.state_spin L st0)
  :
    <<NOFIN: L.(state_sort) st0 <> final>>
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

Lemma spin_noevent
      L st0 e st1
      (STAR: PStar L (fun st => _.(state_sort) st = angelic) st0 [e] st1)
      (SPIN: Beh.state_spin _ st0)
  :
    False
.
Proof.
  remember [e] as tmp in STAR. revert Heqtmp.
  induction STAR; ii; ss. punfold SPIN. rr in STEP; des. inv SPIN; ii; rewrite PROP in *; ss.
  destruct ev, evs; ss; clarify.
  - exploit wf_angelic; et. i; ss.
  - exploit STEP; eauto. i; des; ss. pclearbot. eapply IHSTAR; eauto.
Qed.

Lemma spin_astar
      L st0 st1
      (STAR: PStar L (fun st => _.(state_sort) st = angelic) st0 [] st1)
      (SPIN: Beh.state_spin _ st0)
  :
    <<SPIN: Beh.state_spin _ st1>>
.
Proof.
  remember [] as tmp in STAR. revert Heqtmp.
  revert SPIN. induction STAR; ii; ss.
  { destruct ev, evs; ss. dup SPIN. rr in STEP; des. punfold SPIN. inv SPIN; rewrite PROP in *; ss.
    exploit STEP; eauto. i; des. pclearbot. eapply IHSTAR; ss. }
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
  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.

  Variant _sim sim (i0: idx) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | sim_fin
      (SRT: _.(state_sort) st_src0 = final)
      (SRT: _.(state_sort) st_tgt0 = final)
    :
      _sim sim i0 st_src0 st_tgt0

  | sim_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      i1 ev st_src1 st_tgt1
      (STEP: _.(step) st_src0 (Some (event_sys ev)) st_src1)
      (STEP: _.(step) st_tgt0 (Some (event_sys ev)) st_tgt1)
      (SIM: (sim i1 st_src1 st_tgt1): Prop)
      (* (SIM: forall ev st_tgt1 *)
      (*     (STEP: _.(step) st_tgt0 ev st_tgt1) *)
      (*   , *)
      (*     exists i1 st_src1, <<EVENT: is_some ev>> /\ *)
      (*                        <<STEP: _.(step) st_src0 ev st_src1>> /\ *)
      (*                        <<SIM: sim i1 st_src1 st_tgt1>>) *)
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










  (* | sim_demonic_tgt *)
  (*     (DEM: L1.(state_sort) st_tgt0 = demonic) *)
  (*     (DEMTGT: forall *)
  (*         st_tgt1 *)
  (*         (STEPTGT: L1.(step) st_tgt0 None st_tgt1) *)
  (*       , *)
  (*         exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src0 st_tgt1>>) *)
  (*   : *)
  (*     _sim sim i0 st_src0 st_tgt0 *)
  (* | sim_demonic_src *)
  (*     (DEM: L0.(state_sort) st_src0 = demonic) *)
  (*     (DEMSRC: exists *)
  (*         st_src1 *)
  (*         (STEPSRC: L0.(step) st_src0 None st_src1) *)
  (*       , *)
  (*         exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src1 st_tgt0>>) *)
  (*   : *)
  (*     _sim sim i0 st_src0 st_tgt0 *)
  (* | sim_demonic_both *)
  (*     (DEM: L0.(state_sort) st_src0 = demonic) *)
  (*     (DEM: L1.(state_sort) st_tgt0 = demonic) *)
  (*     (DEMTGT: forall *)
  (*         ev st_tgt1 *)
  (*         (STEPTGT: L1.(step) st_tgt0 ev st_tgt1) *)
  (*       , *)
  (*         exists i1 st_src1, <<ORD: ord i1 i0>> /\ <<STEP: L0.(step) st_src0 ev st_src1>> /\ *)
  (*                                                          <<SIM: sim i1 st_src0 st_tgt0>>) *)
  (*   : *)
  (*     _sim sim i0 st_src0 st_tgt0 *)
  (* | sim_angelic_src *)
  (*     (ANG: L0.(state_sort) st_src0 = angelic) *)
  (*     (ANGSRC: forall *)
  (*         st_src1 *)
  (*         (STEPSRC: L0.(step) st_src0 None st_src1) *)
  (*       , *)
  (*         exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src1 st_tgt0>>) *)
  (*   : *)
  (*     _sim sim i0 st_src0 st_tgt0 *)
  (* | sim_angelic_tgt *)
  (*     (ANG: L1.(state_sort) st_tgt0 = angelic) *)
  (*     (ANGTGT: exists *)
  (*         st_tgt1 *)
  (*         (STEPTGT: L1.(step) st_tgt0 None st_tgt1) *)
  (*       , *)
  (*         exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src0 st_tgt1>>) *)
  (*   : *)
  (*     _sim sim i0 st_src0 st_tgt0 *)
  (* | sim_angelic_both *)
  (*     (ANG: L0.(state_sort) st_src0 = angelic) *)
  (*     (ANG: L1.(state_sort) st_tgt0 = angelic) *)
  (*     (ANGSRC: forall *)
  (*         ev st_src1 *)
  (*         (STEPSRC: L0.(step) st_src0 ev st_src1) *)
  (*       , *)
  (*         exists i1 st_tgt1, <<ORD: ord i1 i0>> /\ <<STEP: L1.(step) st_tgt0 ev st_tgt1>> /\ *)
  (*                                                          <<SIM: sim i1 st_src0 st_tgt0>>) *)
  (*   : *)
  (*     _sim sim i0 st_src0 st_tgt0 *)
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

  Lemma adequacy_tstar
        i0 st_src0 st_tgt0 tr
        (SIM: sim i0 st_src0 st_tgt0)
        (TSTAR: tstar _ st_tgt0 (is_leaf _ /1\ (flip (Beh.of_state _)) tr))
    :
      <<TSTAR: tstar _ st_src0 (is_leaf _ /1\ (flip (Beh.of_state _)) tr)>>
  .
  Proof.
    revert_until i0. pattern i0. eapply well_founded_ind; eauto. clear i0. i.
    rename x into i0. rename H into IH.

    punfold SIM. inv SIM.
    - (** final **)
      inv TSTAR; des; ss; eq_closure_tac.
      econs; eauto. unfold is_leaf, flip in *. des_ifs. esplits; et.
      punfold PROP0. inv PROP0; eq_closure_tac.
      { pfold; econs; eauto. }
      { exploit spin_nofinal; et. i; ss. }
      { pfold; econs; eauto. }
    - (** vis **)
      inv TSTAR; des; ss; eq_closure_tac.
      econs; eauto. unfold is_leaf, flip in *. des_ifs. esplits; et.
      punfold PROP0. inv PROP0; eq_closure_tac.
      { exploit spin_novis; et. i; ss. }
      { pfold; econs; eauto. }
      { determ_tac wf_vis. clear_tac. pfold; econs; eauto.
        rename st1 into st_tgt1. pclearbot. left.
  Abort.

  Lemma adequacy_tstar
        i0 st_src0 st_tgt0 lfs_tgt
        (TSTAR: tstar _ st_tgt0 lfs_tgt)
        (LEAF: lfs_tgt <1= is_leaf _)
        (SIM: sim i0 st_src0 st_tgt0)
    :
      exists lfs_src,
        (<<TSTAR: tstar _ st_src0 lfs_src>>) /\
        (<<LEAF: lfs_src <1= is_leaf _>>) /\
        (<<SIM: forall st_src1 (PR: lfs_src st_src1),
            exists i1 st_tgt1 (PR: lfs_tgt st_tgt1), <<SIM: sim i1 st_src1 st_tgt1>>>>)
  .
  Proof.
    revert_until i0. pattern i0. eapply well_founded_ind; eauto. clear i0. i.
    rename x into i0. rename H into IH.

    punfold SIM. inv SIM.
    - (** final **)
      inv TSTAR; des; ss; eq_closure_tac.
      exists (single st_src0).
      esplits; eauto.
      { econs; eauto. r; ss. }
      { ii. rr in PR; subst. unfold is_leaf. des_ifs. }
      { ii. rr in PR; subst. esplits; eauto. }
    - (** vis **)
      inv TSTAR; des; ss; eq_closure_tac.
      exists (single st_src0).
      esplits; eauto.
      { econs 1; eauto. r; ss. }
      { ii. rr in PR; subst. unfold is_leaf. des_ifs. }
      { ii. rr in PR; subst. esplits; eauto. }
    - (** dsrc **)
      des. pclearbot.
      exploit IH; eauto. i; des.
      esplits; eauto.
      econs 2; eauto.
    - (** dtgt **)
      inv TSTAR; des; ss; eq_closure_tac.
      { apply LEAF in PROP. unfold is_leaf in PROP. des_ifs. }
      exploit SIM0; et. i; des. pclearbot.
      exploit IH; et.
    - (** asrc **)
      (* exists (fun st_src1 => exists ev, _.(step) st_src0 ev st_src1). *)
      exists (fun st_src1 => exists i1 st_tgt1 (PR: lfs_tgt st_tgt1),
                  <<SIM: sim i1 st_src1 st_tgt1>>).
      esplits; eauto.
      + econs 3; eauto. ii. hexploit SIM0; eauto. i; des. pclearbot.
        exploit IH; eauto. i; des.
  Abort.

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
    revert_until i0. pattern i0. eapply well_founded_ind; eauto. clear i0. i.
    rename x into i0. rename H into IH. rename x2 into tr.

    {
      punfold PR. generalize dependent st_src0.
      pattern st_tgt0. pattern tr.
      induction PR using Beh.of_state_ind; ii; ss; rename st0 into st_tgt0.
      - (** done **)
        punfold SIM. inv SIM; try rewrite H in *; ss.
        + (** ff **)
          pfold. econs; eauto.
        + (** d_ **)
          des. pc SIM.
          pfold. econs 6; eauto. rr. esplits; eauto.
          exploit IH. { eauto. } { eauto. } { pfold. econs; eauto. } intro A; des. punfold A.
        + (** a_ **)
          pfold. econs 7; eauto. ii.
          exploit wf_angelic; et. i; clarify.
          esplits; eauto.
          exploit SIM0; eauto. i; des. pc SIM.
          exploit IH. { eauto. } { eauto. } { pfold. econs; eauto. } intro A. punfold A.
      - (** spin **)
        exploit adequacy_spin; eauto.
      - (** ub **)
        punfold SIM. inv SIM; try rewrite H in *; ss.
        + (** d_ **)
          des. pc SIM. pfold. econs 6; eauto. rr. esplits; eauto.
          exploit IH. { eauto. } { eauto. } { pfold. econs 3; eauto. } intro A. punfold A.
        + (** a_ **)
          pfold. econs 7; eauto. ii. exploit wf_angelic; et. i; clarify. esplits; eauto.
          exploit SIM0; eauto. i; des. pc SIM.
          exploit IH. { eauto. } { eauto. } { pfold. econs 3; eauto. } intro A. punfold A.
        + (** _a **)
          des. contradict H0. et.
        + (** aa **)
          pfold. econs 7; eauto. ii. exploit wf_angelic; et. i; clarify. esplits; eauto.
          exploit SIM0; eauto. i; des. pc SIM.
          des. contradict H0. et.
        + (** da **)
          des. contradict H0; et.
      - (** nb **)
        pfold. econs; eauto.
      - (** cons **)
        pc TL.
        punfold SIM. inv SIM; try rewrite SRT in *; ss.
        + (** vv **)
          exploit wf_vis. { eapply SRT. } { eauto. } { eapply STEP. } i; des; clarify.
          pfold. econs 5; eauto. pc SIM0. right. eapply CIH; eauto.
        + (** d_ **)
          des. pc SIM.
          pfold. econs 6; eauto. rr. esplits; eauto.
          exploit IH. { eauto. } { eauto. } { pfold. econs 5; eauto. } intro A. punfold A.
        + (** a_ **)
          pfold. econs 7; eauto. ii.
          exploit wf_angelic; et. i; clarify.
          exploit SIM0; eauto. i; des. pc SIM.
          esplits; eauto.
          exploit IH. { eauto. } { eauto. } { pfold. econs 5; eauto. } intro A. punfold A.
      - (** demonic **)
        rr in STEP. des; clarify. rename st1 into st_tgt1.
        punfold SIM. inv SIM; try rewrite SRT in *; ss.
        + (** d_ **)
          des. pc SIM.
          pfold. econs 6; eauto. rr. esplits; eauto.
          exploit IH. { et. } { et. } { pfold. econs 6; et. rr. esplits; et. } intro A. punfold A.
        + (** _d **)
          exploit SIM0; eauto. i; des. pc SIM. exploit IH; et.
        + (** a_ **)
          pfold. econs 7; eauto. ii.
          exploit wf_angelic; et. i; clarify.
          exploit SIM0; eauto. i; des. pc SIM.
          esplits; eauto.
          exploit IH. { et. } { et. } { pfold. econs 6; et. rr. esplits; et. } intro A. punfold A.
        + (** dd **)
          exploit SIM0; et. i; des. pc SIM.
          exploit IH0. { replace i0 with i1 by admit "TTTTTTTTTTTTTTTT". eauto. } intro A.
          eapply Beh._beh_dstep; et.
        + (** ad **)
          pfold. econs 7; eauto. ii.
          exploit wf_angelic; et. i; clarify.
          exploit SIM0; et. i; des. pc x.
          esplits; eauto.
          exploit IH0. { replace i0 with i1 by admit "TTTTTTTTTTTTTTTT". eauto. } intro A.
          punfold A.
      - (** angelic **)
        admit "TTTTTTTTTTTTTTTT".
  Abort.

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
        pfold. econs; eauto.
      + (** d_ **)
        des. pc SIM.
        pfold. econs 6; eauto. rr. esplits; eauto.
        exploit IH; eauto. intro A. punfold A.
      + (** a_ **)
        pfold. econs 7; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        esplits; eauto.
        exploit SIM0; eauto. i; des. pc SIM.
        exploit IH; eauto. intro A. punfold A.
    - (** spin **)
      exploit adequacy_spin; eauto.
    - (** ub **)
      move i0 before CIH. revert_until i0. pattern i0.
      eapply well_founded_ind; eauto. clear i0. i.
      rename x into i0. rename H into IH.

      punfold SIM. inv SIM; try rewrite H0 in *; ss.
      + (** d_ **)
        des. pc SIM. pfold. econs 6; eauto. rr. esplits; eauto.
        exploit IH; et. intro A. punfold A.
      + (** a_ **)
        pfold. econs 7; eauto. ii. exploit wf_angelic; et. i; clarify. esplits; eauto.
        exploit SIM0; eauto. i; des. pc SIM.
        exploit IH; et. intro A. punfold A.
      + (** _a **)
        des. contradict H0. et.
      + (** aa **)
        pfold. econs 7; eauto. ii. exploit wf_angelic; et. i; clarify. esplits; eauto.
        exploit SIM0; eauto. i; des. pc SIM.
        des. contradict H0. et.
      + (** da **)
        des. contradict H0; et.
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
        pfold. econs 5; eauto. pc SIM0. right. eapply CIH; eauto.
      + (** d_ **)
        des. pc SIM.
        pfold. econs 6; eauto. rr. esplits; eauto.
        exploit IH; et. intro A. punfold A.
      + (** a_ **)
        pfold. econs 7; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i; des. pc SIM.
        esplits; eauto.
        exploit IH; et. intro A. punfold A.
    - (** demonic **)
      rr in STEP. des. clarify. rename st1 into st_tgt1.
    (* move i0 before CIH. revert_until i0. pattern i0. *)
    (* eapply well_founded_ind; eauto. clear i0. i. *)
    (* rename x into i0. rename H into IHi. *)
(* IHi : forall y : idx, *)
(*       ord y i0 -> *)
(*       forall (st_tgt0 : state L1) (evs : Tr.t), *)
(*       state_sort L1 st_tgt0 = demonic -> *)
(*       forall st_tgt1 : state L1, *)
(*       step L1 st_tgt0 None st_tgt1 -> *)
(*       Beh._of_state L1 (upaco2 (Beh._of_state L1) bot2) st_tgt1 evs -> *)
(*       (forall (i0 : idx) (st_src0 : state L0), *)
(*        sim i0 st_src0 st_tgt1 -> paco2 (Beh._of_state L0) r st_src0 evs) -> *)
(*       forall st_src0 : state L0, sim y st_src0 st_tgt0 -> paco2 (Beh._of_state L0) r st_src0 evs *)
      

      move i0 before CIH. move IH before i0. move SRT before i0. revert_until TL.
      pattern i0.
      eapply well_founded_ind; eauto. clear i0. i.
      rename x into i0. rename H into IHi.
      punfold SIM. inv SIM; try rewrite SRT in *; ss.
      + (** d_ **)
        des. pc SIM.
        pfold. econs 6; eauto. rr. esplits; eauto.
        exploit IHi; et. intro A. punfold A.
      + (** _d **)
        exploit SIM0; eauto. i; des. pc SIM. exploit IH; et.
      + (** a_ **)
        pfold. econs 7; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i; des. pc SIM.
        esplits; eauto.
        exploit IHi. { et. } { et. } intro A. punfold A.
      + (** dd **)
        exploit SIM0; et. i; des. pc SIM.
        exploit IH; et. intro A.
        eapply Beh._beh_dstep; et.
      + (** ad **)
        pfold. econs 7; eauto. ii.
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
        pfold. econs 6; eauto. rr. esplits; eauto.
        exploit IHi; et. intro A. punfold A.
      + (** a_ **)
        pfold. econs 7; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i; des. pc SIM.
        esplits; eauto.
        exploit IHi; et. intro A. punfold A.
      + (** _a **)
        des. pc SIM. exploit STEP; et. i; des.
        exploit IH; et.
      + (** aa **)
        pfold. econs 7; eauto. ii.
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
        exploit IHi; et. intro A. punfold A.
        exploit IHi. { et. } { r. et.
        pfold. econs 7; eauto. rr. esplits; eauto.
        exploit IHi; et. intro A. punfold A.
        pfold. econs 7; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i; des. pc SIM.
        esplits; eauto.
        exploit IHi. { et. } { et. } intro A. punfold A.
      + (** dd **)
        exploit SIM0; et. i; des. pc SIM.
        exploit IH; et. intro A.
        eapply Beh._beh_dstep; et.
      + (** ad **)
        pfold. econs 7; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; et. i; des. pc x.
        esplits; eauto.
        exploit IH; et. intro A.
        punfold A.






      + (** a_ **)
        pfold. econs 7; eauto. ii.
        exploit wf_angelic; et. i; clarify.
        exploit SIM0; eauto. i; des. pc SIM.
        esplits; eauto.
        exploit IH. { et. } { et. } { pfold. econs 6; et. rr. esplits; et. } intro A. punfold A.
      + (** dd **)
        exploit SIM0; et. i; des. pc SIM.
        exploit IH0; et. r.
        admit "ABORTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT".
    {
      punfold PR. generalize dependent st_src0.
      induction PR using Beh.of_state_ind; ii; ss; rename st0 into st_tgt0.
      - (** demonic **)
        rr in STEP. des; clarify. rename st1 into st_tgt1.
        punfold SIM. inv SIM; try rewrite SRT in *; ss.
        + (** d_ **)
          des. pc SIM.
          pfold. econs 6; eauto. rr. esplits; eauto.
          exploit IH. { et. } { et. } { pfold. econs 6; et. rr. esplits; et. } intro A. punfold A.
        + (** _d **)
          exploit SIM0; eauto. i; des. pc SIM. exploit IH; et.
        + (** a_ **)
          pfold. econs 7; eauto. ii.
          exploit wf_angelic; et. i; clarify.
          exploit SIM0; eauto. i; des. pc SIM.
          esplits; eauto.
          exploit IH. { et. } { et. } { pfold. econs 6; et. rr. esplits; et. } intro A. punfold A.
        + (** dd **)
          exploit SIM0; et. i; des. pc SIM.
          exploit IH0; et. r.
          admit "ABORTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT".
  Abort.









  }
          
        + (** ad **)
        + (** a_ **)
          pfold. econs 7; eauto. ii.
          exploit wf_angelic; et. i; clarify.
          exploit SIM0; eauto. i; des. pc SIM.
          esplits; eauto.
          exploit IH. { eauto. } { eauto. } { pfold. econs 5; eauto. } intro A. punfold A.
      - (** angelic **)
        pc TL.
        punfold SIM. inv SIM; try rewrite SRT in *; ss.
        + (** vv **)
          exploit wf_vis. { eapply SRT. } { eauto. } { eapply STEP. } i; des; clarify.
          pfold. econs 5; eauto. pc SIM0. right. eapply CIH; eauto.
        + (** d_ **)
          des. pc SIM.
          pfold. econs 6; eauto. rr. esplits; eauto.
          exploit IH. { eauto. } { eauto. } { pfold. econs 5; eauto. } intro A. punfold A.
        + (** a_ **)
          pfold. econs 7; eauto. ii.
          exploit wf_angelic; et. i; clarify.
          exploit SIM0; eauto. i; des. pc SIM.
          esplits; eauto.
          exploit IH. { eauto. } { eauto. } { pfold. econs 5; eauto. } intro A. punfold A.
      -
          exploit IH; eauto.
          pfold. econs 7; eauto. ii. exploit wf_angelic; et. i; clarify. esplits; eauto.
          exploit SIM0; eauto. i; des. pc SIM.
          exploit IH. { eauto. } { eauto. } { pfold. econs 3; eauto. } intro A. punfold A.
        + (** _a **)
          des. contradict H0. et.
        + (** aa **)
          pfold. econs 7; eauto. ii. exploit wf_angelic; et. i; clarify. esplits; eauto.
          exploit SIM0; eauto. i; des. pc SIM.
          des. contradict H0. et.
        + (** da **)
          des. contradict H0; et.
        pfold.
        admit "".
      - (** demonic **)
        admit "".
      - (** angelic **)
        admit "".
    }
          gstep. econs 7; eauto. rr. ii. rename st1 into st_src1.
          exploit STEPSIM; eauto. i; des.
          * destruct ev; ss.
            -- (** some event **) destruct e; ss. right. esplits; eauto.
    }

  Lemma adequacy_tstar
        i0 st_src0 st_tgt0 lfs_tgt
        (TSTAR: tstar _ st_tgt0 lfs_tgt)
        (LEAF: lfs_tgt <1= is_leaf _)
        (SIM: sim i0 st_src0 st_tgt0)
    :
      (<<TSTAR: tstar _ st_src0
                      (fun st_src1 => (<<LEAF: is_leaf _ st_src1>>) /\
                                      (exists i1 st_tgt1 (PR: lfs_tgt st_tgt1),
                                          <<SIM: sim i1 st_src1 st_tgt1>>))>>)
  .
  Proof.
    revert_until i0. pattern i0. eapply well_founded_ind; eauto. clear i0. i.
    rename x into i0. rename H into IH.

    punfold SIM. inv SIM.
    - (** final **)
      inv TSTAR; des; ss; eq_closure_tac.
      econs; eauto. esplits; eauto. unfold is_leaf. des_ifs.
    - (** vis **)
      inv TSTAR; des; ss; eq_closure_tac.
      econs; eauto. esplits; eauto. unfold is_leaf. des_ifs.
    - (** dsrc **)
      des. pclearbot.
      exploit IH; eauto. i; des.
      esplits; eauto.
      econs 2; eauto.
    - (** dtgt **)
      inv TSTAR; des; ss; eq_closure_tac.
      { apply LEAF in PROP. unfold is_leaf in PROP. des_ifs. }
      exploit SIM0; et. i; des. pclearbot.
      exploit IH; et.
    - (** asrc **)
      econs 3; eauto. ii. rename st1 into st_src1. exploit SIM0; eauto. i; des.
      pclearbot. exploit IH; eauto.
    - (** atgt **)
      des. pclearbot.
      exploit IH; try apply SIM; eauto.
      inv TSTAR; des; ss; eq_closure_tac.
      { apply LEAF in PROP. unfold is_leaf in PROP. des_ifs. }
      eapply STEP0; eauto.
    - (** dd **)
      clear IH.
      generalize dependent st_src0. revert_until TSTAR.
      induction TSTAR using tstar_ind2; ii; ss; eauto; eq_closure_tac.
      { apply LEAF in H. unfold is_leaf in H. des_ifs. }
      des.
      exploit SIM0; et. i; des. pclearbot.
      econs 2; eauto. esplits; eauto.
      eapply IH; eauto.



      inv TSTAR; des; ss; eq_closure_tac.
      { apply LEAF in PROP. unfold is_leaf in PROP. des_ifs. }
      exploit SIM0; et. i; des. pclearbot.
      econs 2; eauto. esplits; eauto.
    - (** aa **)
    - (** da **)
    - (** ad **)

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

  Lemma adequacy_final
        i0 st_src0 st_tgt0
        (SIM: sim i0 st_src0 st_tgt0)
        (FIN: Beh.of_state L1 st_tgt0 Tr.done)
    :
      <<FIN: Beh.of_state L0 st_src0 Tr.done>>
  .
  Proof.
    revert_until WF.
    pcofix CIH. i.
    revert_until i0. pattern i0. eapply well_founded_ind; eauto. clear i0. i.
    rename x into i0. rename H into IH.

    punfold FIN. generalize dependent st_src0.
    generalize dependent i0.
    dependent induction FIN using Beh.of_state_ind; ii; ss.
    - (** final **)
      punfold SIM; inv SIM; try rewrite H in *; ss.
      + pfold. econs; eauto.
      + des. pfold. econs 6; eauto. rr. esplits; et. pc SIM. exploit IH; et. intro A. punfold A.
      + pfold. econs 7; eauto. ii. exploit wf_angelic; et. i; clarify.
        exploit SIM0; et. i; des. pc SIM. esplits; et.
        exploit IH; et. intro A. punfold A.
    - (** demonic **)
      rr in STEP. des. clarify.
      punfold SIM; inv SIM; try rewrite DEM in *; ss.
      + des. pfold. econs 6; eauto. rr. esplits; et. pc SIM.
        exploit IH; et. { eapply Beh.beh_dstep; et. } intro A. punfold A.
      + exploit SIM0; et. i; des. pc SIM. exploit IH; et.
      + pfold. econs 7; eauto. ii. exploit wf_angelic; et. i; clarify.
        exploit SIM0; et. i; des. pc SIM. esplits; et.
        exploit IH; et. { eapply Beh.beh_dstep; et. } intro A. punfold A.
      + exploit SIM0; et. i; des. pc SIM.
        pfold. econs 6; et. rr. esplits; et.
        exploit IH0; revgoals.
        { intro A. punfold A. }
        { et. }
        { specialize (IH0 (eq_refl _)). specialize (IH0 i1).
        }
        et. { eapply Beh.beh_dstep; et. } intro A. punfold A.
        pfold. econs 6; et. rr. esplits; et.
        exploit SIM0; et. i; des. pc SIM. exploit IH; et.
      + exploit SIM0; et. i; des. pc SIM. exploit IH; et.
      +
        pfold. econs 7; eauto.
        exploit IH; et. { pfold. econs 6; et. rr. esplits; et. } intro A. punfold A.
      pfold. econs 6; eauto.
      exploit IH; et.
    - (** angelic **)
    punfold SIM; inv SIM.
    - (** final **)
      punfold FIN.
    - (** vis **)
      punfold FIN. inv FIN; rewrite SRT0 in *; ss.
    - (** dsrc **)
      des. pc SIM. pfold. econs 6; eauto. rr. esplits; et. exploit IH; et. intro A. punfold A.
    - (** dtgt **)
      punfold FIN. inv FIN; rewrite SRT in *; ss. rr in STEP. des; clarify.
      exploit SIM0; et. i; des. pc SIM.
      eapply IH; et.
    - (** asrc **)
      pfold. econs 7; et. ii. exploit wf_angelic; et. i; clarify. esplits; et.
      exploit SIM0; et. i; des. pc SIM. exploit IH; et. intro A. punfold A.
    - (** atgt **)
      des. pc SIM. exploit IH; et. eapply Beh.beh_astep; et.
    - (** dd **)
      punfold FIN. inv FIN; try rewrite SRT0 in *; ss. rr in STEP. des; clarify.
      exploit SIM0; et. i; des. pc SIM.
      pfold. econs 6; et. rr. esplits; et.
    - (** aa **)
    - (** da **)
    - (** ad **)
  Qed.

  Lemma adequacy_final
        i0 st_src0 st_tgt0
        (SIM: sim i0 st_src0 st_tgt0)
        (FIN: Beh.of_state L1 st_tgt0 Tr.done)
    :
      <<FIN: Beh.of_state L0 st_src0 Tr.done>>
  .
  Proof.
    revert_until WF.
    (* ginit. *)
    (* { i. eapply cpn2_wcompat; eauto. eapply Beh.of_state_mon. } *)
    (* gcofix CIH. i. *)
    pcofix CIH. i.
    revert_until i0. pattern i0. eapply well_founded_ind; eauto. clear i0. i.
    rename x into i0. rename H into IH.

    punfold SIM; inv SIM.
    (* - (** final **) *)
    (* - (** vis **) *)
    (* - (** dsrc **) *)
    (* - (** dtgt **) *)
    (* - (** asrc **) *)
    (* - (** atgt **) *)
    (* - (** dd **) *)
    (* - (** aa **) *)
    (* - (** da **) *)
    (* - (** ad **) *)
    - (** final **)
      punfold FIN.
    - (** vis **)
      punfold FIN. inv FIN; rewrite SRT0 in *; ss.
    - (** dsrc **)
      des. pc SIM. pfold. econs 6; eauto. rr. esplits; et. exploit IH; et. intro A. punfold A.
    - (** dtgt **)
      punfold FIN. inv FIN; rewrite SRT in *; ss. rr in STEP. des; clarify.
      exploit SIM0; et. i; des. pc SIM.
      eapply IH; et.
    - (** asrc **)
      pfold. econs 7; et. ii. exploit wf_angelic; et. i; clarify. esplits; et.
      exploit SIM0; et. i; des. pc SIM. exploit IH; et. intro A. punfold A.
    - (** atgt **)
      des. pc SIM. exploit IH; et. eapply Beh.beh_astep; et.
    - (** dd **)
      punfold FIN. inv FIN; try rewrite SRT0 in *; ss. rr in STEP. des; clarify.
      exploit SIM0; et. i; des. pc SIM.
      pfold. econs 6; et. rr. esplits; et.
    - (** aa **)
    - (** da **)
    - (** ad **)
  Qed.

  (* Record semantics_wf (L: semantics): Prop := mk_swf { *)
  (*   swf_final: forall st0 (FIN: L.(state_sort) st0 = final),  *)
  (* } *)
  (* . *)

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

    {
      punfold PR. generalize dependent st_src0.
      induction PR using Beh.of_state_ind; ii; ss;
        rename st0 into st_tgt0.
      - (** done **)
        punfold SIM. inv SIM; try rewrite H in *; ss.
        + (** fin-fin **)
          gstep. econs; eauto.
        + (** asim **)
          gstep. econs 7; eauto. rr. ii. rename st1 into st_src1.
          exploit STEPSIM; eauto. i; des.
          * destruct ev; ss.
            -- (** some event **) destruct e; ss. right. esplits; eauto.
    }

    destruct (classic (tr = Tr.spin)); clarify.
    { punfold PR.
      move PR before IH. revert_until PR.
      dependent induction PR using Beh.of_state_ind; ii; ss.
      - exploit adequacy_spin; eauto. i. gstep. econs; eauto.
      - rr in STEP. des. clarify. gstep.
        rename st0 into st_tgt0. rename st1 into st_tgt1.
        specialize (IH0 (eq_refl _)).
        inv TL; ii; ss.
        econs 5; et. admit.
      - admit.
    }

    dup SIM.
    punfold SIM. inv SIM.
    - gstep. punfold PR. inv PR; ss; try rewrite FINTGT in *; clarify.
      (** fin **) econs; ss; et.

    - punfold PR.
      inv PR; ss; try rewrite DEM in *; clarify.
      + (** nb **) gstep; econs; eauto.
      + (** dem tau **)
        rr in STEP. des. clarify.
        exploit STEPSIM; et. i; des; subst; r in SIM; des; ss; et.
        inv PLUS.
        destruct ev, evs; ss.
        inv STAR.
        { gstep. econs 5; eauto. rr. esplits; eauto. econs; eauto.
      + (** dem sys **)
        rr in STEP. des. clarify. r in TL; des; ss.
        exploit STEPSIM; et. i; des; subst; r in SIM; des; ss.
        inv PLUS.
        destruct ev0; ss; clarify.
        *
          gstep. econs 6; eauto. rr. esplits; eauto.
          admit.
        *
          gstep. econs 5; eauto. rr. esplits; eauto.
          admit.

    -
        gstep.
        pfold.
        (*** st_tgt0 --ev--> st_tgt1 ---> evs
             st_src0
         ***)
        eapply IH; eauto. pfold. econs; eauto.
        pfold. econs 6; eauto. eapply IH; eauto.

    - punfold PR.

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
