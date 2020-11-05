Require Import sflib.
Require Import Universe.
Require Import Semantics.
Require Import Behavior.
From Paco Require Import paco.
Require Import RelationClasses List.
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.

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
  - exploit STEP; eauto. i; des; ss.
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




Section SIM.

  Variable L0 L1: semantics.

  Definition rec (ind coind: bool -> bool -> L0.(state) -> L1.(state) -> Prop)
             b_src b_tgt st_src0 st_tgt0 :=
    (<<COIND: match b_src, b_tgt with
              | false, false => <<COIND: coind true true st_src0 st_tgt0>>
              | _, _ => False
              end>>)
    \/ (<<IND: ind b_src b_tgt st_src0 st_tgt0>>)
  .

  Inductive _sim sim b_src b_tgt (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  (* | sim_final *)
  (*     (FINTGT: _.(state_sort) st_tgt0 = final) *)
  (*     (FINSRC: _.(state_sort) st_src0 = final) *)
  (*   : *)
  (*     _sim sim i0 st_src0 st_tgt0 *)

  (* | sim_demonic *)
  (*     (DEM: _.(state_sort) st_tgt0 = demonic) *)
  (*     (STEP: forall *)
  (*         ev st_tgt1 *)
  (*         (STEPTGT: _.(step) st_tgt0 ev st_tgt1) *)
  (*       , *)
  (*         exists i1 st_src1, *)
  (*           (<<PLUS: DPlus _ st_src0 ev st_src1>> *)
  (*            \/ (<<TAU: st_src1 = st_src0>> /\ <<TAU: ev = None>> /\ <<ORD: ord i1 i0>>)) *)
  (*           /\ *)
  (*           (<<SIM: sim i1 st_src1 st_tgt1>>)) *)
  (*   : *)
  (*     _sim sim i0 st_src0 st_tgt0 *)
  (* | sim_angelic *)
  (*     (ANG: _.(state_sort) st_src0 = angelic) *)
  (*     (STEP: forall *)
  (*         ev st_src1 *)
  (*         (STEPSRC: _.(step) st_src0 ev st_src1) *)
  (*       , *)
  (*         exists i1 st_tgt1, *)
  (*           (<<PLUS: APlus _ st_tgt0 ev st_tgt1>> *)
  (*            \/ (<<TAU: st_tgt1 = st_tgt0>> /\ <<TAU: ev = None>> /\ <<ORD: ord i1 i0>>)) *)
  (*           /\ *)
  (*           (<<SIM: sim i1 st_src1 st_tgt1>>)) *)
  (*   : *)
  (*     _sim sim i0 st_src0 st_tgt0 *)
  | sim_final
      (FINTGT: _.(state_sort) st_tgt0 = final)
      (FINSRC: _.(state_sort) st_src0 = final)
    :
      _sim sim b_src b_tgt st_src0 st_tgt0
  | sim_demonic_tgt
      (DEM: L1.(state_sort) st_tgt0 = demonic)
      (STEP: forall
          st_tgt1
          (STEPTGT: L1.(step) st_tgt0 None st_tgt1)
        ,
          <<SIM: rec (_sim sim) sim b_src false st_src0 st_tgt1>>)
    :
      _sim sim b_src b_tgt st_src0 st_tgt0
  | sim_demonic_src
      (DEM: L0.(state_sort) st_src0 = demonic)
      (STEP: exists
          st_src1
          (STEPSRC: L0.(step) st_src0 None st_src1)
        ,
          <<SIM: rec (_sim sim) sim false b_tgt st_src1 st_tgt0>>)
    :
      _sim sim b_src b_tgt st_src0 st_tgt0
  | sim_event
      (DEM: L0.(state_sort) st_src0 = demonic)
      (DEM: L1.(state_sort) st_tgt0 = demonic)
      (STEP: forall
          ev st_tgt1
          (STEPTGT: L1.(step) st_tgt0 ev st_tgt1)
        ,
          exists st_src1, (<<STEPSRC: L0.(step) st_src0 ev st_src1>>) /\
                          (<<SIM: rec (_sim sim) sim false false st_src1 st_tgt1>>))
    :
      _sim sim b_src b_tgt st_src0 st_tgt0
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

  Theorem sim_ind :
forall (sim P: bool -> bool -> state L0 -> state L1 -> Prop),
       (* (b_src b_tgt : bool) (st_src0 : state L0) (st_tgt0 : state L1), *)
  (forall b_src b_tgt st_src0 st_tgt0
          (FINTGT: state_sort L1 st_tgt0 = final)
          (FINSRC: state_sort L0 st_src0 = final)
    ,
      P b_src b_tgt st_src0 st_tgt0)
  ->
  (forall b_src b_tgt st_src0 st_tgt0
      (DEM: state_sort L1 st_tgt0 = demonic)
      (STEP: forall st_tgt1,
          step L1 st_tgt0 None st_tgt1 ->
          <<SIM: rec (_sim sim /4\ P) sim b_src false st_src0 st_tgt1 >>)
    ,
      P b_src b_tgt st_src0 st_tgt0)
  ->
  (forall b_src b_tgt st_src0 st_tgt0
      (DEM: state_sort L0 st_src0 = demonic)
      (STEP: exists st_src1 (_ : step L0 st_src0 None st_src1),
          <<SIM: rec (_sim sim /4\ P) sim false b_tgt st_src1 st_tgt0 >>)
    ,
      P b_src b_tgt st_src0 st_tgt0)
  ->
  (forall b_src b_tgt st_src0 st_tgt0
      (DEM: state_sort L0 st_src0 = demonic)
      (DEM: state_sort L1 st_tgt0 = demonic)
      (STEP: forall ev st_tgt1,
          step L1 st_tgt0 ev st_tgt1 ->
          exists st_src1 : state L0,
            <<STEPTGT: step L0 st_src0 ev st_src1 >> /\
                       <<SIM: rec (_sim sim /4\ P) sim false false st_src1 st_tgt1 >>)
    ,
      P b_src b_tgt st_src0 st_tgt0)
  ->
   forall b_src b_tgt st_src0 st_tgt0,
     _sim sim b_src b_tgt st_src0 st_tgt0 -> P b_src b_tgt st_src0 st_tgt0.
  Proof.
    fix IH 11. i. inv H3.
    - eapply H; eauto.
    - eapply H0; eauto. ii. exploit STEP; et. i; des. esplits; eauto.
      rr. rr in x. des; et. right.
      esplits; et. eapply IH; et.
    - eapply H1; eauto. ii. des. esplits; eauto.
      rr. rr in SIM. des; et. right.
      esplits; et. eapply IH; et.
    - eapply H2; eauto. ii. exploit STEP; eauto. i; des. esplits; eauto.
      rr. rr in SIM. des; et. right.
      esplits; et. eapply IH; et.
  Qed.

  Definition sim: _ -> _ -> _ -> _ -> Prop := paco4 _sim bot4.

  Lemma sim_mon: monotone4 _sim.
  Proof.
    {
      ii. induction IN using sim_ind; ii; ss.
      - econs 1; et.
      - econs 2; et. ii. exploit STEP; eauto. i; des.
        rr. rr in x. des_ifs; des; ss; et.
      - econs 3; et. des. esplits; et.
        rr. rr in SIM. des_ifs; des; ss; et.
      - econs 4; et. ii. exploit STEP; eauto. i; des.
        unfold rec. rr in SIM. des_ifs; des; ss; et. esplits; eauto.
    }
  Qed.

  Hint Constructors _sim.
  Hint Unfold sim.
  Hint Resolve sim_mon: paco.

  Lemma adequacy_spin
        b_src b_tgt st_src0 st_tgt0
        (SIM: sim b_src b_tgt st_src0 st_tgt0)
        (SPIN: Beh.state_spin L1 st_tgt0)
    :
      <<SPIN: Beh.state_spin L0 st_src0>>
  .
  Proof.
    revert_until L1.
    ginit.
    { i. eapply cpn1_wcompat; eauto. eapply Beh.state_spin_mon. }
    gcofix CIH. i.

    destruct (classic (b_src = false /\ b_tgt = false)).
    { des; clarify.
      punfold SIM. inv SIM.
    }

    punfold SIM.
    induction SIM using sim_ind.
    - exploit spin_nofinal; eauto. i; ss.
    - punfold SPIN. inv SPIN; rewrite DEM in *; ss. des. clarify.
      rename st1 into st_tgt1.
      exploit STEP; eauto. pclearbot. i; des. rr in x. des.
      + des_ifs. des. rr in COIND; des; ss.
        admit.
      + eapply IND0; eauto.
    -
      { clarify. eapply IH; eauto. }
      rr in STEP; des.
      gstep. econs 2; eauto. esplits; eauto. gbase. eapply CIH; eauto.
    -
    eapply 
    revert_until i0. pattern i0. eapply well_founded_ind; eauto. clear i0. i.
    rename x into i0. rename H into IH.

    punfold SIM. inv SIM.
    (* - eapply spin_nofinal in SPIN; ss. *)
    - punfold SPIN. inv SPIN; rewrite DEM in *; ss. des. clarify.
      rename st1 into st_tgt1.
      exploit STEP; eauto. pclearbot. i; des; rr in SIM; des; ss; cycle 1.
      { clarify. eapply IH; eauto. }
      rr in STEP; des.
      gstep. econs 2; eauto. esplits; eauto. gbase. eapply CIH; eauto.
    - gstep. econs; eauto. ii. exploit STEP; eauto. i; des; ss; clarify; rr in SIM; des; ss; cycle 1.
      { rename st1 into st_src1. esplits; eauto. exploit IH; eauto.
        ii. eapply gpaco1_mon_gen; eauto. { eapply Beh.state_spin_mon. } ii; ss.
      }
      rr in STEP0; des.
      punfold SPIN. inv SPIN; ss; rewrite PROP in *; ss.
      exploit STEP0; eauto. i; des. clarify. rr in TL; des; ss. clarify.
      rename st1 into st_src1. esplits; eauto.
      gbase. eapply CIH; eauto.
  Qed.

  Lemma adequacy_final
        (WF: well_founded ord)
        i0 st_src0 st_tgt0
        (SIM: sim i0 st_src0 st_tgt0)
        (FIN: Beh.of_state L1 st_tgt0 Tr.done)
    :
      <<FIN: Beh.of_state L0 st_src0 Tr.done>>
  .
  Proof.
    punfold SIM; inv SIM.
    - punfold FIN.
      generalize dependent st_src0.
      generalize dependent i0.
      dependent induction FIN using Beh.of_state_ind; ii; try rewrite DEM in *; ss;
        rename st0 into st_tgt0.
      rr in STEP. des. clarify. rename st1 into st_tgt1.
      exploit STEP; eauto. i; des.
      + rr in STEP; des; ss. rr in SIM; des; ss. exploit IH; ss; eauto.
      +
      apply FIN0 in FINAL.

      inv FIN; try rewrite DEM in *; ss.
      rr in STEP. des. clarify. inv TL.
      apply FIN0 in FINAL.
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
          exploit STEP; eauto. i; des.
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
        exploit STEP; et. i; des; subst; r in SIM; des; ss; et.
        inv PLUS.
        destruct ev, evs; ss.
        inv STAR.
        { gstep. econs 5; eauto. rr. esplits; eauto. econs; eauto.
      + (** dem sys **)
        rr in STEP. des. clarify. r in TL; des; ss.
        exploit STEP; et. i; des; subst; r in SIM; des; ss.
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
