From compcert Require Import Smallstep Clight Integers Events Behaviors.
Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import Imp.
Require Import Imp2Clight.

Set Implicit Arguments.






(************************ Coq Aux ****************************)
(************************ Coq Aux ****************************)
(************************ Coq Aux ****************************)
Fixpoint sequence X (xs: list (option X)): option (list X) :=
  match xs with
  | nil => Some nil
  | Some hd :: tl => do tl <- (sequence tl); Some (hd :: tl)
  | None :: _ => None
  end
.

(*** it is basically sequence with return type (Err (list X) (list X)). ***)
(*** i.e., fails with information ***)
Fixpoint squeeze X (es: list (option X)): ((list X) * bool) :=
  match es with
  | [] => ([], true)
  | Some e :: tl => let '(es, succ) := squeeze tl in ((e :: es), succ)
  | _ => ([], false)
  end
.

Definition option_to_list X (x: option X): list X :=
  match x with
  | Some x => [x]
  | _ => []
  end
.
Coercion option_to_list: option >-> list.
Hint Constructors Forall2.

(************************ Tgt Aux ****************************)
(************************ Tgt Aux ****************************)
(************************ Tgt Aux ****************************)
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

(************************ Src Aux ****************************)
(************************ Src Aux ****************************)
(************************ Src Aux ****************************)

Section STAR.
  Variable L: semantics.
  Variable P: L.(state) -> Prop.
  Inductive pstar: L.(state) -> list event -> L.(state) -> Prop :=
  | star_refl: forall st_src0 (P: P st_src0), pstar st_src0 [] st_src0
  | star_step: forall
      st_src0 es0 st_src1 es1 st_src2
      (P: P st_src0)
      (HD: step L st_src0 es0 st_src1)
      (TL: pstar st_src1 es1 st_src2)
    ,
      pstar st_src0 (es0 ++ es1) st_src2
  .
End STAR.
Definition dstar L := pstar L (fun st_src0 => L.(state_sort) st_src0 = demonic).
Definition star L := pstar L top1.

Lemma star_des
      L
      st0 e es st2
      (STAR: star L st0 (e :: es) st2)
  :
    exists st1, <<HD: star L st0 [e] st1>> /\ <<TL: star L st1 es st2>>
.
Proof.
  remember (e :: es) as x. revert Heqx. revert e es.
  induction STAR; ii; ss.
  destruct es0; ss.
  - clarify. esplits; et. change [e] with ((option_to_list (Some e)) ++ []).
    econs; ss; et. econs; ss; et.
  - subst. exploit IHSTAR; et. i; des. esplits; et.
    change [e] with ((@option_to_list event None) ++ [e]).
    econs; ss; et.
Qed.

Lemma star_event_ind
      L
      (P: L.(state) -> list event -> L.(state) -> Prop)
      (BASE: forall st0 st1, star L st0 [] st1 -> P st0 [] st1)
      (SUCC: forall e es st0 st1 st2, star L st0 [e] st1 -> star L st1 es st2 ->
                                      P st1 es st2 -> P st0 (e :: es) st2)
  :
    forall st0 es st1, star L st0 es st1 -> P st0 es st1
.
Proof.
  fix IH 2.
  i.
  destruct es; ss.
  - eapply BASE. ss.
  - eapply star_des in H. des. rename st2 into st_mid.
    eapply SUCC.
    { et. }
    { et. }
    eapply IH.
    eapply TL.
Qed.

Definition NoStuck L (st_src0: state L): Prop :=
  L.(state_sort) st_src0 = angelic ->
  (<<NOSTUCK: exists ev st_src1, step L st_src0 ev st_src1>>)
(* (<<DTM: forall st_src1 st_src1', *)
(*     step L st_src0 None st_src1 -> *)
(*     step L st_src0 None st_src1' -> *)
(*     st_src1 = st_src1'>>) *)
.

(************************ Decompile ****************************)
(************************ Decompile ****************************)
(************************ Decompile ****************************)

Definition decompile_eval (ev: eventval): option val :=
  match ev with
  | EVlong i => Some (Vint (Int64.signed i))
  | _ => None
  end
.

Definition decompile_event (ev: Events.event): option event :=
  match ev with
  | Event_syscall fn evs ev =>
    do vs <- sequence (List.map decompile_eval evs);
    do v <- decompile_eval ev;
    Some (event_sys fn vs v)
  | _ => None
  end.

(* Definition _decompile_trinf decompile_trinf (tr: traceinf): Tr.t := *)
(*   match tr with *)
(*   | Econsinf ev tr => *)
(*     match decompile_event ev with *)
(*     | Some ev => Tr.cons ev (decompile_trinf tr) *)
(*     | _ => Tr.ub *)
(*     end *)
(*   end *)
(* . *)

(* CoFixpoint decompile_trinf (tr: traceinf): Tr.t := *)
(*   _decompile_trinf decompile_trinf tr. *)
CoFixpoint decompile_trinf (tr: traceinf): Tr.t :=
  match tr with
  | Econsinf ev tr =>
    match decompile_event ev with
    | Some ev => Tr.cons ev (decompile_trinf tr)
    | _ => Tr.ub
    end
  end
.

Lemma unfold_decompile_trinf
      tr
  :
    (decompile_trinf tr) = 
    (match tr with
     | Econsinf ev tr =>
       match decompile_event ev with
       | Some ev => Tr.cons ev (decompile_trinf tr)
       | _ => Tr.ub
       end
     end)
.
Proof.
  admit "mid - define bisim on Tr.t and add axiom: bisim -> eq".
Qed.

Lemma decompile_trinf_app
      tr_tgt tr_src T
      (MB: squeeze (List.map decompile_event tr_tgt) = (tr_src, true))
  :
    (decompile_trinf (tr_tgt *** T)) = Tr.app tr_src (decompile_trinf T)
.
Proof.
  ginduction tr_tgt; ii; ss; clarify.
  des_ifs. ss.
  rewrite unfold_decompile_trinf. des_ifs. f_equal.
  eapply IHtr_tgt; ss.
Qed.

Definition transl_beh (p: program_behavior): Tr.t :=
  match p with
  | Terminates tr i =>
    let '(es, succ) := squeeze (List.map decompile_event tr) in
    Tr.app es (if succ then (Tr.done (Int.signed i)) else Tr.ub)
  | Diverges tr => 
    let '(es, succ) := squeeze (List.map decompile_event tr) in
    Tr.app es (if succ then (Tr.spin) else Tr.ub)
  | Reacts tr => (decompile_trinf tr)
  | Goes_wrong tr =>
    let '(es, succ) := squeeze (List.map decompile_event tr) in
    Tr.app es Tr.ub
  end
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

Lemma match_event_iff
      e_src e_tgt
  :
    decompile_event e_tgt = Some e_src <->
    match_event e_tgt e_src
.
Proof.
  admit "ez".
Qed.

Lemma match_event_squeeze
      e_src e_tgt
  :
    squeeze [decompile_event e_tgt] = ([e_src], true) <->
    match_event e_tgt e_src
.
Proof.
  split; i.
  - ss. des_ifs. eapply match_event_iff; et.
  - eapply match_event_iff in H; et. ss. des_ifs.
Qed.

Lemma match_events_squeeze
      es_src es_tgt
  :
    squeeze (List.map decompile_event es_tgt) = (es_src, true) <->
    Forall2 match_event es_tgt es_src
.
Proof.
  admit "ez - remove match_event and just use decompile_event?".
Qed.

Theorem decompile_trinf_spec
        tr
  :
    match_beh (Reacts tr) (decompile_trinf tr)
.
Proof.
  revert tr.
  pcofix CIH.
  i. destruct tr; ss.
  rewrite unfold_decompile_trinf. des_ifs.
  - eapply match_event_iff in Heq. dup Heq. inv Heq.
    pfold. eapply match_beh_Reacts; et.
  - pfold. econsr; ss; et.
    r. esplits; ss; et. rewrite behavior_app_E0. ss.
Qed.









Definition improves2 {L0 L1} (st_src0: L0.(STS.state)) (st_tgt0: L1.(Smallstep.state)): Prop :=
  forall tr_tgt (BEH: state_behaves L1 st_tgt0 tr_tgt),
  exists tr_src, (<<BEH: (Beh.of_state L0 st_src0) tr_src>>) /\
                 (<<SIM: match_beh tr_tgt tr_src>>)
.



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

  Definition safe_along_events (st_src0: state L0) (tr: list Events.event): Prop := forall
      st_src1
      tx ty tx_src
      (STAR: star L0 st_src0 tx_src st_src1)
      (MB: squeeze (List.map decompile_event tx) = (tx_src, true))
      (PRE: tx ++ ty = tr)
    ,
      <<SAFE: NoStuck L0 st_src1>>
  .

  Definition safe_along_trace (st_src0: state L0) (tr: program_behavior) : Prop := forall
      thd
      (BEH: behavior_prefix thd tr)
    ,
      safe_along_events st_src0 thd
  .

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
    { ss. }
  Qed.

  Lemma safe_along_events_star
        st_src0 st_src1 es0_src es0 es1
        (STAR: star L0 st_src0 es0_src st_src1)
        (MB: squeeze (List.map decompile_event es0) = (es0_src, true))
        (SAFE: safe_along_events st_src0 (es0 ++ es1))
    :
      <<SAFE: safe_along_events st_src1 es1>>
  .
  Proof.
    revert_until STAR. revert es1. revert es0.
    admit "mid - TODO: use star tail induction".
  (*   induction STAR; i; ss. *)
  (*   { destruct es0; ss. des_ifs. } *)
  (*   destruct es0; ss. *)
  (*   - eapply safe_along_events_step_some; et. *)
  (*   - *)
  (*   ii. des; clarify. eapply SAFE; ss. *)
  (*   { econs; et. } *)
  (*   { instantiate (1 := e0 :: _). ss. des_ifs. rewrite MB0 in *; clarify. } *)
  (*   { esplits; et. ss. } *)
  (* Qed. *)
  Qed.

  Definition wf (L: semantics): Prop :=
    forall (st0: L.(state)) (ANG: L.(state_sort) st0 = angelic),
    forall st1 st1' (STEP: step L st0 None st1) (STEP: step L st0 None st1'), st1 = st1'
  .

  Hypothesis WFSRC: wf L0.

  Lemma simulation_star
        i0 st_src0 tr_tgt st_tgt1 st_tgt0
        (* (MATCH: Forall2 match_event tr_tgt tr_src) *)
        (STEP: Star L1 st_tgt0 tr_tgt st_tgt1)
        (SIM: sim i0 st_src0 st_tgt0)
        (SAFE: safe_along_events st_src0 tr_tgt)
    :
      exists i1 st_src1 tr_src,
        (<<MB: squeeze (List.map decompile_event tr_tgt) = (tr_src, true)>>) /\
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

  (*** TODO: move to proper place? ***)
  Lemma _beh_astep_rev
        r tr st0 ev st1
        (SRT: _.(state_sort) st0 = angelic)
        (STEP: _.(step) st0 ev st1)
        (BEH: paco2 (Beh._of_state L0) r st1 tr)
    :
      <<BEH: paco2 (Beh._of_state L0) r st0 tr>>
  .
  Proof.
    exploit wf_angelic; et. i; clarify.
    pfold. econsr; ss; et. rr. ii. exploit wf_angelic; et. i; des. subst.
    exploit WFSRC; [..|apply STEP|apply STEP0|]; ss. i; subst. esplits; et.
    punfold BEH.
  Qed.

  Lemma _beh_astep_rev'
        cpn rg r tr st0 ev st1
        (SRT: _.(state_sort) st0 = angelic)
        (STEP: _.(step) st0 ev st1)
        (* (BEH: gpaco2 (Beh._of_state L0) cpn rg r st1 tr) *)
        (BEH: paco2 (Beh._of_state L0) r st1 tr)
    :
      <<BEH: gpaco2 (Beh._of_state L0) cpn rg r st0 tr>>
  .
  Proof.
    exploit wf_angelic; et. i; clarify.
    gstep. econsr; ss; et. rr. ii. exploit wf_angelic; et. i; des. subst.
    exploit WFSRC; [..|apply STEP|apply STEP0|]; ss. i; subst. esplits; et.
    punfold BEH. eapply Beh.of_state_mon; et. ii; ss. gfinal. r in PR. des; ss; et.
  Qed.

  Lemma beh_of_state_star_progress
        cpn rg r st_src0 st_src1 es0 tr1
        (BEH: gpaco2 (Beh._of_state L0) cpn (rg \2/ r) r st_src1 tr1)
        (STAR: star L0 st_src0 es0 st_src1)
        (PROG: es0 <> [])
    :
      <<BEH: gpaco2 (Beh._of_state L0) cpn rg r st_src0 (Tr.app es0 tr1)>>
  .
  Proof.
    revert BEH. revert tr1. revert PROG.
    induction STAR; ii; ss.
    destruct (state_sort L0 st_src0) eqn:T.
    - exploit wf_angelic; et. i; subst. ss.
      eapply IHSTAR in BEH; ss. des.
      eapply _beh_astep_rev'; et.
    - exploit wf_demonic; et. i; subst. ss.
      pfold. econs; ss; et. rr. esplits; ss; et. punfold U.
    - admit "ez - wf_final; final nostep".
    - destruct es0; ss; cycle 1.
      { admit "ez - wf_vis; vis should always make some event". }
      pfold; econs; ss; et.
    (* revert BEH. revert tr1. revert PROG. *)
    (* induction STAR using star_event_ind; ii; ss. *)
    (* clear_tac. *)
    (* destruct es; ss. *)
    (* { admit "star_single". } *)
    (* eapply IHSTAR1 in BEH; ss. des. *)
    (* { admit "star_single". } *)
  Qed.

  Lemma beh_of_state_star
        st_src0 st_src1 es0 tr1
        (BEH: (Beh.of_state L0) st_src1 tr1)
        (STAR: star L0 st_src0 es0 st_src1)
    :
      <<BEH: (Beh.of_state L0) st_src0 (Tr.app es0 tr1)>>
  .
  Proof.
    revert BEH. revert tr1.
    induction STAR; ii; ss.
    exploit IHSTAR; et. intro U; des.
    destruct (state_sort L0 st_src0) eqn:T.
    - exploit wf_angelic; et. i; subst. ss.
      eapply _beh_astep_rev; et.
    - exploit wf_demonic; et. i; subst. ss.
      pfold. econs; ss; et. rr. esplits; ss; et. punfold U.
    - admit "ez - wf_final; final nostep".
    - destruct es0; ss; cycle 1.
      { admit "ez - wf_vis; vis should always make some event". }
      pfold; econs; ss; et.
  Qed.

  Lemma adequacy
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
          eapply beh_of_state_star; ss; et.
          cut (Beh.of_state L0 st_src1 (Tr.done (Int.signed r))); ss.
          (* assert(SAFE0: safe_along_trace st_src1 (Terminates tr r)). *)
          assert(SAFE0: safe_along_events st_src1 []).
          { clear - SAFE STEP MB.
            r in SAFE. specialize (SAFE tr).
            hexploit1 SAFE.
            { eexists (Terminates nil _). ss. unfold Eapp. rewrite List.app_nil_r. ss. }
            eapply safe_along_events_star; et.
            rewrite List.app_nil_r. ss.
          }
          clear - SAFE0 WFSRC FIN WF SIM0.
          revert_until i1. pattern i1. eapply well_founded_ind; et. clear i1. intros i0 IH.
          i. punfold SIM0. inv SIM0.
          * pfold. econs; ss; et. admit "ez".
          * des. admit "ez - final nostep".
          * des. pclearbot.
            exploit IH; et. { eapply safe_along_events_step_none; et. } intro U.
            eapply Beh.beh_dstep; ss; et.
          * des. admit "ez - final nostep".
          * destruct (classic (exists ev st_src2, step L0 st_src1 ev st_src2)).
            { des. exploit wf_angelic; et. i; subst. exploit SIM; et. i; des.
              pclearbot.
              exploit IH; et. { eapply safe_along_events_step_none; et. } i; des.
              eapply _beh_astep_rev; ss; et. }
            contradict H. eapply SAFE0; et.
            { econs; ss; et. }
            { instantiate (1:=[]). ss. }
            { esplits; ss. }
          * des. admit "ez - final nostep".
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
      - admit "mid - prove this! (diverge case)".
      - (* forever_reactive *)
        (rename T into tr).
        esplits; et.
        + rename H into BEH. ss.
          ginit. { eapply cpn2_wcompat; eauto with paco. } revert_until WFSRC. gcofix CIH. i.
          inv BEH.
          rename s2 into st_tgt1. rename t into tr_tgt. rename H into STAR.
          hexploit simulation_star; try apply STAR; et.
          { eapply SAFE. exists (Reacts T). ss. }
          i; des.

          erewrite decompile_trinf_app; et.
          gbase.
          eapply beh_of_state_star; ss; et.
          right.
          TTTTTTTTTTTTTTTTTTT
          rr.
          pfold.
          left.
          rewrite MB in *. clarify.



          (*** 1. Lemma: star + Beh.of_state -> Beh.of_state app ***)
          (*** 2. wf induction on i1 ***)
          eapply beh_of_state_star; ss; et.
          (* assert(SAFE0: safe_along_trace st_src1 (Terminates tr r)). *)
          assert(SAFE0: safe_along_events st_src1 []).
          { clear - SAFE STEP MB.
            r in SAFE. specialize (SAFE tr).
            hexploit1 SAFE.
            { eexists (Terminates nil _). ss. unfold Eapp. rewrite List.app_nil_r. ss. }
            eapply safe_along_events_star; et.
            rewrite List.app_nil_r. ss.
          }
          clear - SAFE0 WFSRC FIN WF SIM0.
          revert_until i1. pattern i1. eapply well_founded_ind; et. clear i1. intros i0 IH.
          i. punfold SIM0. inv SIM0.
        + eapply decompile_trinf_spec.
      - admit "mid - prove this! (goes_wrong case)".
    }
    { (*** unsafe ***)
      assert(NOTSAFE:
               exists st_src1 thd thd_tgt,
                 (<<B: behavior_prefix thd_tgt tr_tgt>>)
                 /\ (<<MB: squeeze (List.map decompile_event thd_tgt) = (thd, true)>>)
                 /\ (<<STAR: star L0 st_src0 thd st_src1>>)
                 /\ (<<STUCK: ~NoStuck L0 st_src1>>)).
      { unfold safe_along_trace in SAFE. Psimpl. des.
        unfold safe_along_events in *. Psimpl. des.
        Psimpl. des. Psimpl. des.
        subst.
        esplits; try apply SAFE1; ss; et.
        clear - SAFE.
        r in SAFE. des; subst. r. eexists (behavior_app _ _).
        rewrite <- behavior_app_assoc. ss; et.
      }
      des.
      exists (Tr.app thd Tr.ub). esplits; ss.
      - clear - WFSRC STAR STUCK.
        eapply beh_of_state_star; et. unfold NoStuck in *.
        repeat (Psimpl; des; unfold NW in *). clears st_src0. clear st_src0.
        pfold. econsr; ss; et. ii. exploit wf_angelic; ss; et. i; subst. exfalso.
        exploit STUCK0; ss; et.
      - r in B. des. subst. clear - MB.
        ginduction thd_tgt; ii; ss; clarify.
        { ss. pfold. econsr; ss; et.
          { r. esplits; ss; et. }
        }
        des_ifs. ss.
        eapply match_event_iff in Heq.
        eapply match_beh_cons; ss; et. rewrite <- behavior_app_assoc. ss.
    }
  Qed.

End SIM.
Hint Constructors _sim.
Hint Unfold sim.
Hint Resolve sim_mon: paco.
