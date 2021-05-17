From compcert Require Import Smallstep Clight Integers Events Behaviors.
Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import Imp.
Require Import Imp2Clight.

Set Implicit Arguments.

(******* TODO: move to Behavior.v && remove redundancy with SimSTS.v *********)
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










(* Section BEH. *)

(* Variable L: Smallstep.semantics. *)
(* Inductive _state_behaves2 (state_behaves2: L.(Smallstep.state) -> program_behavior -> Prop): *)
(*   L.(Smallstep.state) -> program_behavior -> Prop := *)
(* (*   state_terminates : forall (t : trace) (s' : Smallstep.state L) (r : int), *) *)
(* (*                      Star L s t s' -> Smallstep.final_state L s' r -> state_behaves L s (Terminates t r) *) *)
(* (* | state_diverges : forall (t : trace) (s' : Smallstep.state L), *) *)
(* (*                    Star L s t s' -> Forever_silent L s' -> state_behaves L s (Diverges t) *) *)
(* (* | state_reacts : forall T : traceinf, Forever_reactive L s T -> state_behaves L s (Reacts T) *) *)
(* (* | state_goes_wrong : forall (t : trace) (s' : Smallstep.state L), *) *)
(* (*                      Star L s t s' -> *) *)
(* (*                      Nostep L s' -> (forall r : int, ~ Smallstep.final_state L s' r) -> state_behaves L s (Goes_wrong t) *) *)
(* | sb2_final *)
(*     st0 retv *)
(*     (FINAL: Smallstep.final_state L st0 retv) *)
(*   : *)
(*     _state_behaves2 state_behaves2 st0 (Terminates E0 retv) *)
(* | sb2_spin *)
(*     st0 *)
(*     (SPIN: Forever_silent L st0) *)
(*   : *)
(*     _state_behaves2 state_behaves2 st0 (Diverges E0) *)
(* | sb2_step *)
(* | sb2_syscall *)
(* | sb2_stuck *)
(* (* | sb_nb *) *)
(* (*     st0 *) *)
(* (*   : *) *)
(* (*     _of_state of_state st0 (Tr.nb) *) *)
(* (* | sb_vis *) *)
(* (*     st0 st1 ev evs *) *)
(* (*     (SRT: L.(state_sort) st0 = vis) *) *)
(* (*     (STEP: _.(step) st0 (Some ev) st1) *) *)
(* (*     (TL: of_state st1 evs) *) *)
(* (*   : *) *)
(* (*     _of_state of_state st0 (Tr.cons ev evs) *) *)
(* (* | sb_demonic *) *)
(* (*     st0 *) *)
(* (*     evs *) *)
(* (*     (SRT: L.(state_sort) st0 = demonic) *) *)
(* (*     (STEP: union st0 (fun e st1 => (<<HD: e = None>>) /\ (<<TL: _of_state of_state st1 evs>>))) *) *)
(* (*   : *) *)
(* (*     _of_state of_state st0 evs *) *)
(* (* | sb_angelic *) *)
(* (*     st0 *) *)
(* (*     evs *) *)
(* (*     (SRT: L.(state_sort) st0 = angelic) *) *)
(* (*     (STEP: inter st0 (fun e st1 => (<<HD: e = None>>) /\ (<<TL: _of_state of_state st1 evs>>))) *) *)
(* (*   : *) *)
(* (*     _of_state of_state st0 evs *) *)
(* . *)



(* Definition single_events_at (L: Smallstep.semantics) (s:L.(Smallstep.state)) : Prop := *)
(*   forall t s', Step L s t s' -> (List.length t <= 1)%nat. *)

(* Record strict_determinate_at (L: Smallstep.semantics) (s:L.(Smallstep.state)) : Prop := *)
(*   Strict_determinate_at { *)
(*       ssd_determ_at: forall t1 s1 t2 s2 *)
(*         (STEP0: Step L s t1 s1) *)
(*         (STEP1 :Step L s t2 s2), *)
(*         <<EQ: t1 = t2>> /\ <<EQ: s1 = s2>>; *)
(*     ssd_determ_at_final: forall tr s' retv *)
(*         (FINAL: Smallstep.final_state L s retv) *)
(*         (STEP: Step L s tr s'), *)
(*         False; *)
(*     ssd_traces_at: *)
(*       single_events_at L s *)
(*   }. *)

Definition single_events_at (L: Smallstep.semantics) (s:L.(Smallstep.state)) : Prop :=
  forall t s', Step L s t s' -> (t = E0).

Record strict_determinate_at (L: Smallstep.semantics) (s:L.(Smallstep.state)) : Prop :=
  Strict_determinate_at {
      ssd_determ_at: forall t1 s1 t2 s2
        (STEP0: Step L s t1 s1)
        (STEP1 :Step L s t2 s2),
        <<EQ: s1 = s2>>;
    ssd_determ_at_final: forall tr s' retv
        (FINAL: Smallstep.final_state L s retv)
        (STEP: Step L s tr s'),
        False;
    ssd_traces_at:
      single_events_at L s
  }.

Section SIM.

  Variable L0: STS.semantics.
  Variable L1: Smallstep.semantics.
  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.

  Local Open Scope smallstep_scope.

  Variant _sim sim (i0: idx) (st_src0: L0.(STS.state)) (st_tgt0: L1.(Smallstep.state)): Prop :=
  | sim_fin
      retv
      (RANGE: (0 <= retv <= Int.max_unsigned)%Z)
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(Smallstep.final_state) st_tgt0 (Int.repr retv))
      (DTM: True) (*** TODO: copy-paste sd_final_determ in Smallstep.v ***)
    :
      _sim sim i0 st_src0 st_tgt0

  (* | sim_vis *)
  (*     (SRT: _.(state_sort) st_src0 = vis) *)
  (*     (SRT: _.(state_sort) st_tgt0 = vis) *)
  (*     (SIM: forall ev st_tgt1 *)
  (*         (STEP: _.(step) st_tgt0 (Some ev) st_tgt1) *)
  (*       , *)
  (*         exists st_src1 (STEP: _.(step) st_src0 (Some ev) st_src1), *)
  (*           <<SIM: exists i1, sim i1 st_src1 st_tgt1>>) *)
  (*   : *)
  (*     _sim sim i0 st_src0 st_tgt0 *)

  | sim_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src1 st_tgt0>>)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_demonic_tgt_dtm
      (*** WRONG DEF, Note: UB in tgt ***)
      (* (SIM: forall st_tgt1 *)
      (*     (STEP: Step L1 st_tgt0 E0 st_tgt1) *)
      (*   , *)
      (*     exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src0 st_tgt1>>) *)
      (DTM: strict_determinate_at L1 st_tgt0)
      (SIM: exists st_tgt1
          (STEP: Step L1 st_tgt0 E0 st_tgt1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src0 st_tgt1>>)
      (*** equivalent def ***)
      (* st_tgt1 *)
      (* (STEP: Step L1 st_tgt0 E0 st_tgt1) *)
      (* i1 *)
      (* (ORD: ord i1 i0) *)
      (* (SIM: sim i1 st_src0 st_tgt1) *)
    :
      _sim sim i0 st_src0 st_tgt0
  | sim_angelic_src
      (SRT: _.(state_sort) st_src0 = angelic)
      (SIM: forall st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src1 st_tgt0>>)
    :
      _sim sim i0 st_src0 st_tgt0


  | sim_demonic_both
      (SRT: _.(state_sort) st_src0 = demonic)
      (DTM: strict_determinate_at L1 st_tgt0)
      (SIM: exists st_tgt1
          (STEP: Step L1 st_tgt0 E0 st_tgt1)
        ,
          exists st_src1 (STEP: _.(step) st_src0 None st_src1),
            <<SIM: exists i1, sim i1 st_src1 st_tgt1>>)
    :
      _sim sim i0 st_src0 st_tgt0
  .

  Definition sim: _ -> _ -> _ -> Prop := paco3 _sim bot3.

  Lemma sim_mon: monotone3 _sim.
  Proof.
    ii. inv IN.

    - econs 1; et.
    - econs 2; et. des. esplits; et.
    - econs 3; et. des. esplits; et.
    - econs 4; et. i. exploit SIM; et. i; des. esplits; et.
    - econs 5; et. des. esplits; et.
  Qed.

  Hint Constructors _sim.
  Hint Unfold sim.
  Hint Resolve sim_mon: paco.

  Record simulation: Prop := mk_simulation {
    sim_wf_ord: <<WF: well_founded ord>>;
    sim_init: forall st_tgt0 (INITT: L1.(Smallstep.initial_state) st_tgt0),
        exists i0, (<<SIM: sim i0 L0.(initial_state) st_tgt0>>);
    (* sim_init: exists i0 st_tgt0, (<<SIM: sim i0 L0.(initial_state) st_tgt0>>) /\ *)
    (*                              (<<INITT: L1.(Smallstep.initial_state) st_tgt0>>); *)
    (* sim_dtm: True; *)
  }
  .

  Hypothesis WF: well_founded ord.

  Ltac pc H := rr in H; desH H; ss.

  Lemma adequacy_spin
        i0 st_src0 st_tgt0
        (SIM: sim i0 st_src0 st_tgt0)
        (SPIN: Forever_silent L1 st_tgt0)
    :
      <<SPIN: Beh.state_spin L0 st_src0>>
  .
  Proof.
    (* revert_until WF. *)
    (* ginit. *)
    (* { i. eapply cpn1_wcompat; eauto. eapply Beh.state_spin_mon. } *)
    (* gcofix CIH. i. *)
    (* revert_until i0. pattern i0. eapply well_founded_ind; eauto. clear i0. i. *)
    (* rename x into i0. rename H into IH. *)

    (* punfold SIM. inv SIM. *)
    (* - (** final **) *)
    (*   des. exfalso. punfold SPIN. inv SPIN; rewrite SRT1 in *; ss. *)
    (* - (** vis **) *)
    (*   des. exfalso. punfold SPIN. inv SPIN; rewrite SRT1 in *; ss. *)
    (* - (** vis stuck **) *)
    (*   exfalso. punfold SPIN. inv SPIN; rewrite SRT0 in *; ss. *)
    (* - (** dsrc **) *)
    (*   des. pc SIM. gstep. econs 2; et. esplits; et. gbase. et. *)
    (* - (** dtgt **) *)
    (*   punfold SPIN. inv SPIN; try rewrite SRT in *; ss. des; clarify. *)
    (*   pc TL. exploit wf_demonic; et; i; clarify. *)
    (*   exploit SIM0; et. i; des. pc SIM. eapply IH; et. *)
    (* - (** asrc **) *)
    (*   punfold SPIN. inv SPIN; ss. *)
    (*   + gstep. econs 1; et. ii. *)
    (*     exploit L0.(wf_angelic); et. i; clarify. esplits; et. *)
    (*     exploit SIM0; et. i; des. pc SIM. *)
    (*     gbase. eapply CIH; eauto. *)
    (*   + des; clarify. rename st1 into st_tgt1. *)
    (*     exploit wf_demonic; et; i; clarify. *)
    (*     gstep. econs; et. ii. exploit wf_angelic; et; i; clarify. *)
    (*     pc TL. exploit SIM0; et. i; des. pc SIM. *)
    (*     (* gbase. eapply CIH; et. pfold; econs 2; et. esplits; et. *) *)
    (*     eapply gpaco1_mon. { eapply IH; et. pfold; econs 2; et. esplits; et. } { ss. } { ss. } *)
    (* - (** atgt **) *)
    (*   des. pc SIM. eapply IH; eauto. eapply spin_astep; et. *)
    (* - (** dd **) *)
    (*   punfold SPIN. inv SPIN; rewrite SRT0 in *; ss. des. *)
    (*   exploit wf_demonic; et; i; clarify. pc TL. *)
    (*   exploit SIM0; et. i; des. pc SIM. *)
    (*   gstep. econs 2; et. esplits; et. gbase. eapply CIH; et. *)
    (* - (** aa **) *)
    (*   punfold SPIN. inv SPIN; rewrite SRT0 in *; ss. des. *)
    (*   gstep. econs; et. ii. *)
    (*   exploit L0.(wf_angelic); et; i; clarify. *)
    (*   exploit SIM0; et. i; des. pc SIM. *)
    (*   gbase. eapply CIH; et. eapply spin_astep; et. *)
    (* - (** da **) *)
    (*   des. pc SIM. gstep. econs 2; et. esplits; et. gbase. eapply CIH; et. eapply spin_astep; et. *)
    (* - (** ad **) *)
    (*   gstep. econs 1; et. ii. *)
    (*   exploit L0.(wf_angelic); et; i; clarify. *)
    (*   punfold SPIN. inv SPIN; rewrite SRT0 in *; ss. des; clarify. pc TL. *)
    (*   exploit (wf_demonic); et; i; clarify. *)
    (*   exploit SIM0; et. i; des. pc x. *)
    (*   gbase. eapply CIH; et. *)
    admit "TODO - hard".
  Qed.

  Definition improves2 (st_src0: L0.(STS.state)) (st_tgt0: L1.(Smallstep.state)): Prop :=
    (* forall tr_tgt (BEH: state_behaves L1 st_tgt0 tr_tgt), *)
    (* exists tr_src, (<<BEH: (Beh.of_state L0 st_src0) tr_src>>) /\ *)
    (*                (<<SIM: match_beh tr_tgt tr_src>>) *)
    forall tr_tgt tr_src (SIM: match_beh tr_tgt tr_src) (BEH: state_behaves L1 st_tgt0 tr_tgt),
      (<<BEH: (Beh.of_state L0 st_src0) tr_src>>)
  .
  (* UB (O) *)
  (* print "A" *)

  (* print "A" (O, ub is top) *)
  (* print "A" *)

  (* print "B" (X, filtered by match_beh) *)
  (* print "A" *)


  (*** TODO: put this outside of the section ***)
  Hint Constructors _match_beh.
  Hint Unfold match_beh.
  Hint Resolve match_beh_mon: paco.

  Lemma sim_step_rev
        st_src0 st_tgt0 st_tgt1 i0
        (STEP: Step L1 st_tgt0 E0 st_tgt1)
        (SIM: sim i0 st_src0 st_tgt0) (*** src0 >= tgt0 ***)
    :
      (* forall i1 (LT: ord i1 i0), sim i1 st_src0 st_tgt1 (*** src0 >= tgt1 ***) *)
      sim i0 st_src0 st_tgt1 (*** src0 >= tgt1 ***)
  .
  Proof.
    revert_until WF. pcofix CIH. i.
    i. punfold SIM. bar. inv SIM.
    - exfalso. admit "ez - final nostep".
    - des. pclearbot.
      pfold. eapply sim_demonic_src; et. esplits; et.
    - des. pclearbot. assert(st_tgt1 = st_tgt2). { admit "ez - determinate". } subst.
      admit "ez - ord mon".
    - pfold. eapply sim_angelic_src; et. ii. exploit SIM0; et. i; des. pclearbot. esplits; et.
    -des. pclearbot. assert(st_tgt1 = st_tgt2). { admit "ez - determinate". } subst.
     pfold. eapply sim_demonic_both; et.
  Abort.
  (*** counter example: i0 is 0. SIM can simulate using demonic_both, but the goal can't ***)

  Variable kappa: idx.
  Lemma sim_step_rev
        st_src0 st_tgt0 st_tgt1 i0
        (STEP: Step L1 st_tgt0 E0 st_tgt1)
        (SIM: sim i0 st_src0 st_tgt0) (*** src0 >= tgt0 ***)
    :
      sim kappa st_src0 st_tgt1 (*** src0 >= tgt1 ***)
  .
  Proof.
    admit "somehow".
  Qed.

  Lemma adequacy_aux
        i0 st_src0 st_tgt0
        (SIM: sim i0 st_src0 st_tgt0)
    :
      <<IMPR: improves2 st_src0 st_tgt0>>
  .
  Proof.
    rr.
    revert_until WF.
    pcofix CIH. i.
    rename SIM0 into M.

    inv BEH.
    - (rename H into STAR; rename s' into st_tgt1).
      move STAR before CIH. revert_until STAR. induction STAR; ii; ss; cycle 1.
      { subst.
        assert(t1 = E0 \/ exists ev, t1 = [ev]).
        { admit "ez - single_events". }
        des.
        - subst. ss. eapply IHSTAR; et. eapply sim_step_rev; et.
        - subst. ss. eapply IHSTAR; et.
          { pfold. eapply sim_demonic_tgt_dtm; et.
            { admit "ez - tau state is strict_determinate". }
            esplits; et.
            econsr; et.
        subst.
    -

    move i0 before CIH. move M at bottom. revert_until i0. pattern i0.
    eapply well_founded_ind; eauto. clear i0. i. rename H into IH.
    punfold M. inv M.
    - punfold SIM. bar. inv SIM; ss; clarify.
      + pfold. econs; eauto.
        inv BEH; ss. assert(r0 = Int.repr retv) by admit "ez". subst.
        rewrite Int.unsigned_repr; ss.
      + des. pclearbot.
        hexploit IH; try apply SIM; et. intro T.
        eapply Beh._beh_dstep; et.
      + des. pclearbot.
        hexploit IH; try apply SIM. et.
        instantiate (1:=Terminates tr r0).
        { clear - BEH DTM STEP. admit "ez - if it is hard let me know; there should be some similar proof in compcert". }
        { et. }
        { et. }
      + pfold. econsr; et. rr. ii. exploit wf_angelic; et. i; subst. esplits; et.
        hexploit SIM0; et. i; des. pclearbot.
        hexploit IH; try apply SIM; et. intro T. punfold T.
      + des. pclearbot.
        admit "Probably I am doing it wrong; just inv state_behaves and do induction on STAR".
    - inv BEH. rename H0 into STAR. rename s' into st_tgt1. move STAR before IH. revert_until STAR.
      revert x.
      induction STAR; i; cycle 1.
      { subst.
        assert(t1 = E0 \/ exists ev, t1 = [ev]).
        { admit "ez - single_events". }
        des.
        - subst. ss. eapply IHSTAR. et.
        admit "???".
      }
      inv MT; ss.

      punfold SIM. inv SIM; ss; clarify.
      + exfalso. clear - SRT0 H1. admit "ez".
        pfold. eapply Beh.sb_demonic; ss. rr. esplits; et. 
        right.
        pfold.
        eapply Beh._beh_dstep; et.
        eapply CIH.
        eapply Beh._beh_astep; et.
        destruct (classic ( des. pclearbot.
        hexploit IH; try apply SIM; et. intro T.
        eapply Beh._beh_dstep; et.
        et.
        et.
        et.
        { rewrite <- behavior_app_E0. eapply state_behaves_app. et.
          { econs; et. }
          eapply star_one; et.
        }
        try apply BEH; et. intro T.
        
        { et. }
        { r. eapply SIM.
        try apply SIM. et. pfold. eapply sim_demonic_src; et. econsr; eauto.
    generalize dependent st_src0. generalize dependent i0.
    induction M using Beh.of_state_ind; ii; ss; rename st0 into st_tgt0.
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
        specialize (SIM0 ev st1). apply SIM0 in STEP; clear SIM0; des.
        pfold. econs 4; eauto. pc SIM. right. eapply CIH; eauto.
      + (** vis stuck **)
        apply STUCK in STEP. clarify.
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
