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

  | sim_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: exists _ev_tgt _st_tgt1, Step L1 st_tgt0 [_ev_tgt] _st_tgt1)
      (SIM: forall ev_tgt st_tgt1
          (STEP: Step L1 st_tgt0 ev_tgt st_tgt1)
        ,
          exists st_src1 ev_src (STEP: _.(step) st_src0 (Some ev_src) st_src1),
            (<<MATCH: Forall2 match_event ev_tgt [ev_src]>>) /\
            (<<SIM: exists i1, sim i1 st_src1 st_tgt1>>))
    :
      _sim sim i0 st_src0 st_tgt0

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
    - econs 2; et. i. exploit SIM; et. i; des. esplits; et.
    - econs 3; et. des. esplits; et.
    - econs 4; et. des. esplits; et.
    - econs 5; et. i. exploit SIM; et. i; des. esplits; et.
    - econs 6; et. des. esplits; et.
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

  Definition improves2 (st_src0: L0.(STS.state)) (st_tgt0: L1.(Smallstep.state)): Prop :=
    forall tr_tgt (BEH: state_behaves L1 st_tgt0 tr_tgt),
    exists tr_src, (<<BEH: (Beh.of_state L0 st_src0) tr_src>>) /\
                   (<<SIM: match_beh tr_tgt tr_src>>)
  .

  Definition decompile_eval (ev: eventval): option val :=
    match ev with
    | EVlong i => Some (Vint (Int64.signed i))
    | _ => None
    end
  .

  Definition sequence X (xs: list (option X)): option (list X) := admit "ez".

  Definition decompile_event (ev: Events.event): option event :=
    match ev with
    | Event_syscall fn evs ev =>
      do vs <- sequence (List.map decompile_eval evs);
      do v <- decompile_eval ev;
      Some (event_sys fn vs v)
    | _ => None
    end.

  CoFixpoint decompile_trinf (tr: traceinf): Tr.t :=
    match tr with
    | Econsinf ev tr =>
      match decompile_event ev with
      | Some ev => Tr.cons ev (decompile_trinf tr)
      | _ => Tr.done 42 (*** ub? nb? spin? ***)
      end
    end
  .

  (* Definition transl_beh (p: program_behavior): option Tr.t := *)
  (*   match p with *)
  (*   | Terminates tr i => *)
  (*     do es <- sequence (List.map decompile_event tr); *)
  (*     Some (Tr.app es (Tr.done (Int.signed i))) *)
  (*   | Diverges tr =>  *)
  (*     do es <- sequence (List.map decompile_event tr); *)
  (*     Some (Tr.app es (Tr.spin)) *)
  (*   | Reacts tr => Some (decompile_trinf tr) *)
  (*   | Goes_wrong tr => *)
  (*     do es <- sequence (List.map decompile_event tr); *)
  (*     Some (Tr.app es (Tr.ub)) *)
  (*   end *)
  (* . *)

  Fixpoint distill (es: list (option event)): ((list event) * bool) :=
    match es with
    | [] => ([], true)
    | Some e :: tl => let '(es, succ) := distill tl in ((e :: es), succ)
    | _ => ([], false)
    end
  .

  Definition transl_beh (p: program_behavior): Tr.t :=
    match p with
    | Terminates tr i =>
      let '(es, succ) := distill (List.map decompile_event tr) in
      Tr.app es (if succ then (Tr.done (Int.signed i)) else Tr.ub)
      (* let es := (filter_map decompile_event tr) in *)
      (* (Tr.app es (Tr.done (Int.signed i))) *)
    | Diverges tr => 
      let es := (filter_map decompile_event tr) in
      (Tr.app es (Tr.spin))
    | Reacts tr => (decompile_trinf tr)
    | Goes_wrong tr =>
      let es := (filter_map decompile_event tr) in
      (Tr.app es (Tr.ub))
    end
  .

  Definition option_to_list X (x: option X): list X :=
    match x with
    | Some x => [x]
    | _ => []
    end
  .
  Coercion option_to_list: option >-> list.

  Section STAR.
    Variable L: semantics.
    Variable P: L.(state) -> Prop.
    Inductive pstar: L.(state) -> list event -> L.(state) -> Prop :=
    | star_refl: forall st_src0 (P: P st_src0), pstar st_src0 [] st_src0
    | star_step: forall
        st_src0 tr0 st_src1 tr1 st_src2
        (P: P st_src0)
        (HD: step L st_src0 tr0 st_src1)
        (TL: pstar st_src1 tr1 st_src2)
      ,
        pstar st_src0 (tr0 ++ tr1) st_src2
    .
  End STAR.
  Definition dstar L := pstar L (fun st_src0 => L.(state_sort) st_src0 = demonic).
  Definition star L := pstar L top1.

  Definition NoStuck L (st_src0: state L): Prop :=
    L.(state_sort) st_src0 = angelic ->
    (<<NOSTUCK: exists ev st_src1, step L st_src0 ev st_src1>>)
    (* (<<DTM: forall st_src1 st_src1', *)
    (*     step L st_src0 None st_src1 -> *)
    (*     step L st_src0 None st_src1' -> *)
    (*     st_src1 = st_src1'>>) *)
  .

  Definition safe_along_events (st_src0: state L0) (tr: list Events.event) : Prop := forall
      st_src1
      tx tx_src
      (STAR: star L0 st_src0 tx_src st_src1)
      (MB: distill (List.map decompile_event tx) = (tx_src, true))
      (PRE: exists ty, tx ++ ty = tr)
    ,
      <<SAFE: NoStuck L0 st_src1>>
  .

  Definition safe_along_trace (st_src0: state L0) (tr: program_behavior) : Prop := forall
      thd
      (BEH: behavior_prefix thd tr)
    ,
      safe_along_events st_src0 thd
  .

  Lemma decompile_match_event
        e0 e1
        (D: decompile_event e0 = Some e1)
    :
      <<M: match_event e0 e1>>
  .
  Proof.
    destruct e0; ss. uo. des_ifs.
    admit "ez".
  Qed.

  Hint Resolve match_beh_mon: paco.

  Hint Constructors Forall2.

  Lemma match_beh_cons
        b0 b1
        e0 e1
        b0_ b1_
        (B0_: b0_ = (behavior_app [e0] b0))
        (B1_: b1_ = (Tr.app [e1] b1))
        (M0: match_beh b0 b1)
        (M1: match_event e0 e1)
    :
      <<M: match_beh b0_ b1_>>
  .
  Proof.
    subst.
    revert_until b0. revert b0.
    pcofix CIH. i. punfold M0. inv M0.
    - pfold. econs 1; try refl; ss; et.
    - pfold. econs 2; try refl; ss; et.
    - pfold. econs 3; try refl; ss; et. pclearbot. right.
      change (Reacts (Econsinf ev trinf)) with (behavior_app [ev] (Reacts trinf)).
      eapply CIH; et.
    - pfold. econs 4.
      { instantiate (1:=e1 :: mtr). ss; et. }
      { econs; ss; et. }
      rr in TB. des. subst.
      rr. esplits; ss; et. rewrite <- behavior_app_assoc. ss.
  Qed.

  Lemma match_val_inj
        v_tgt0 v_src0 v_src1
        (M0: match_val v_tgt0 v_src0)
        (M1: match_val v_tgt0 v_src1)
    :
      v_src0 = v_src1
  .
  Proof. inv M0. inv M1. ss. Qed.

  Lemma match_event_inj
        e_tgt0 e_src0 e_src1
        (M0: match_event e_tgt0 e_src0)
        (M1: match_event e_tgt0 e_src1)
    :
      e_src0 = e_src1
  .
  Proof.
    inv M0. inv M1. f_equal.
    { clear - MV MV1. ginduction MV; ii; ss.
      { inv MV1; ss. }
      inv MV1; ss.
      f_equal; et.
      eapply match_val_inj; et.
    }
    eapply match_val_inj; et.
  Qed.

  Lemma safe_along_events_step_some
        st_src0 st_src1 e_src e0 es0
        (STEP: step L0 st_src0 (Some e_src) st_src1)
        (MB: decompile_event e0 = Some e_src)
        (SAFE: safe_along_events st_src0 ([e0] ++ es0))
    :
      <<SAFE: safe_along_events st_src1 es0>>
  .
  Proof.
    ii. des; clarify. eapply SAFE; ss.
    { econs; et. }
    { instantiate (1 := e0 :: _). ss. des_ifs. rewrite MB0 in *; clarify. }
    { esplits; et. ss. }
  Qed.

  Lemma safe_along_events_step_none
        st_src0 st_src1 es0
        (STEP: step L0 st_src0 None st_src1)
        (SAFE: safe_along_events st_src0 es0)
    :
      <<SAFE: safe_along_events st_src1 es0>>
  .
  Proof.
    ii. des; clarify. eapply SAFE; ss.
    { econs; et. }
    { ss. et. }
    { esplits; et. }
  Qed.

  Definition wf (L: semantics): Prop :=
    forall (st0: L.(state)) (ANG: L.(state_sort) st0 = angelic),
    forall st1 st1' (STEP: step L st0 None st1) (STEP: step L st0 None st1), st1 = st1'
  .

  Hypothesis WFSRC: wf L0.

  Lemma match_event_iff
        e_src e_tgt
    :
      decompile_event e_tgt = Some e_src <->
      match_event e_tgt e_src
  .
  Proof.
    admit "ez".
  Qed.

  Lemma match_event_distill
        e_src e_tgt
    :
      distill [decompile_event e_tgt] = ([e_src], true) <->
      match_event e_tgt e_src
  .
  Proof.
    split; i.
    - ss. des_ifs. eapply match_event_iff; et.
    - eapply match_event_iff in H; et. ss. des_ifs.
  Qed.

  Lemma match_events_distill
        es_src es_tgt
    :
      distill (List.map decompile_event es_tgt) = (es_src, true) <->
      Forall2 match_event es_tgt es_src
  .
  Proof.
    admit "ez - remove match_event and just use decompile_event".
  Qed.

  Lemma simulation_star
        i0 st_src0 tr_tgt st_tgt1 st_tgt0
        (* (MATCH: Forall2 match_event tr_tgt tr_src) *)
        (STEP: Star L1 st_tgt0 tr_tgt st_tgt1)
        (SIM: sim i0 st_src0 st_tgt0)
        (SAFE: safe_along_events st_src0 tr_tgt)
    :
      exists i1 st_src1 tr_src,
        (<<MB: distill (List.map decompile_event tr_tgt) = (tr_src, true)>>) /\
        (<<STEP: star L0 st_src0 tr_src st_src1>>) /\
        (<<SIM: sim i1 st_src1 st_tgt1>>)
  .
  Proof.
    revert SAFE. revert SIM. revert st_src0. revert i0.
    induction STEP; ii; ss.
    { esplits; et. econs; ss. }
    subst. rename s1 into st_tgt0. rename s2 into st_tgt1. rename s3 into st_tgt2.
    rename t1 into tr_tgt0. rename t2 into tr_tgt1.

    revert_until i0. pattern i0. eapply well_founded_ind; et. clear i0. intros i0 IH. i.

    punfold SIM. inv SIM.
    - (* fin *)
      admit "ez - final nostep".
    - (* vis *)
      clear SRT0. exploit SIM0; et. i; des. pclearbot.
      inv MATCH; ss. inv H4; ss. rename H3 into MB. eapply match_event_iff in MB. des_ifs.
      exploit IHSTEP; et. { eapply safe_along_events_step_some; et. } i; des. clarify.
      esplits; et. rewrite cons_app.
      change [ev_src] with (option_to_list (Some ev_src)).
      econs; et.
    - (* dsrc *)
      des. pclearbot. exploit IH; et. { eapply safe_along_events_step_none; et. } i; des.
      esplits; et.
      rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
    - (* dtgt *)
      des. pclearbot. exploit ssd_determ_at; [et|apply H|apply STEP0|]. i; des. subst.
      exploit ssd_traces_at; [et|apply H|]. i; subst. clear_tac.
      exploit IHSTEP; et.
    - (* asrc *)
      exploit SAFE; try apply SRT.
      { econs; et. }
      { instantiate (1:=[]). ss. }
      { esplits; et. rewrite app_nil_l. ss. }
      i; des.
      exploit wf_angelic; et. i; subst.
      exploit SIM0; et. i; des. pclearbot.
      exploit IH; et. { eapply safe_along_events_step_none; et. } i; des.
      esplits; et.
      rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
    - (* dboth *)
      des. pclearbot.
      exploit ssd_determ_at; [et|apply H|apply STEP0|]. i; des. subst.
      exploit ssd_traces_at; [et|apply H|]. i; subst. clear_tac.
      exploit IHSTEP; et. { eapply safe_along_events_step_none; et. } i; des.
      esplits; et. rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
  Qed.

  Lemma adequacy_aux
        i0 st_src0 st_tgt0
        (SIM: sim i0 st_src0 st_tgt0)
    :
      <<IMPR: improves2 st_src0 st_tgt0>>
  .
  Proof.
    ii.
    (* set (transl_beh tr_tgt) as tr_src in *. *)
    destruct (classic (safe_along_trace st_src0 tr_tgt)); rename H into SAFE.
    { (*** safe ***)
      exists (transl_beh tr_tgt).
      inv BEH.
      - (rename t into tr; rename H into STAR; rename s' into st_tgt1; rename H0 into FIN).
        esplits; et.
        + ss. des_ifs_safe.
          hexploit simulation_star; try apply STAR; et.
          { eapply SAFE. exists (Terminates [] r). ss. unfold Eapp. rewrite app_nil_r; ss. }
          i; des.
          rewrite MB in *. clarify.



          (*** 1. Lemma: star + Beh.of_state -> Beh.of_state app ***)
          (*** 2. wf induction on i1 ***)


          clears st_tgt0. clear st_tgt0.
          revert SAFE. revert SIM0. revert i0.
          induction STEP; ii; ss.
          { admit "do reasoning...". }
          subst. rename s1 into st_tgt0. rename s2 into st_tgt1. rename s3 into st_tgt2.
          rename t1 into tr_tgt0. rename t2 into tr_tgt1.

          punfold SIM0. inv SIM0; ss.
          * admit "?".
          * des. admit "ez - final nostep".
          *
        + ss.
          clear - SAFE SIM.
          clear.
          induction tr; ii; ss.
          { pfold. econs; ss; et. admit "ez - change def". }
          destruct (decompile_event a) eqn:T.
          * des_ifs_safe.
            eapply match_beh_cons; ss.
            { instantiate (1:=Terminates tr r). instantiate (1:=a). ss. }
            { ss. }
            { eapply decompile_match_event; ss. }
          * des_ifs_safe. ss. pfold; econsr; et; ss. r. esplits; et.
            rewrite behavior_app_E0; et.
      -
            }

          des_ifs.
          { eapply decompile_match_event in Heq; des. ss.
            eapply match_beh_cons; ss.
            { instantiate (1:=Terminates tr r). instantiate (1:=a). ss. }
            { ss. }
            ss.
          }
          { eapply IHtr.
      -
    }
    { (*** unsafe ***)
    }
    exists (transl_beh tr_tgt).
    { (rename H into STAR; rename s' into st_tgt1; rename H0 into STK0; rename H1 into STK1).
    }
    - .
  Qed.

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
