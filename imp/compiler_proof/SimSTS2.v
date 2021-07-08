From compcert Require Import Smallstep Clight Integers Events Behaviors.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import Imp.
Require Import Imp2Csharpminor.
From Ordinal Require Import Ordinal.

Set Implicit Arguments.





Section Beh.

  Inductive match_val : eventval -> Z -> Prop :=
  | match_val_intro :
      forall v, match_val (EVlong v) (Int64.signed v).

  Inductive match_event : Events.event -> STS.event -> Prop :=
  | match_event_intro
      name eargs uargs er ur
      (MV: Forall2 match_val eargs uargs)
      (MV: match_val er ur)
    :
      match_event (Event_syscall name eargs er) (event_sys name uargs↑ ur↑)
  .

  Variant _match_beh (match_beh: _ -> _ -> Prop) (tgtb : program_behavior) (srcb : Tr.t) : Prop :=
  | match_beh_Terminates
      tr mtr r
      (MT : Forall2 match_event tr mtr)
      (TB : tgtb = Terminates tr r)
      (SB : srcb = Tr.app mtr (Tr.done r.(Int.intval)↑))
    :
      _match_beh match_beh tgtb srcb
  | match_beh_Diverges
      tr mtr
      (MT : Forall2 match_event tr mtr)
      (TB : tgtb = Diverges tr)
      (SB : srcb = Tr.app mtr (Tr.spin))
    :
      _match_beh match_beh tgtb srcb
  | match_beh_Reacts
      ev mev trinf mtrinf
      (ME : match_event ev mev)
      (MB : match_beh (Reacts trinf) mtrinf)
      (TB : tgtb = Reacts (Econsinf ev trinf))
      (SB : srcb = Tr.cons mev mtrinf)
    :
      _match_beh match_beh tgtb srcb
  | match_beh_ub_trace
      mtr tr
      (SB : srcb = Tr.app mtr (Tr.ub))
      (MT : Forall2 match_event tr mtr)
      (TB : behavior_prefix tr tgtb)
    :
      _match_beh match_beh tgtb srcb.

  Definition match_beh : _ -> _ -> Prop := paco2 _match_beh bot2.

  Lemma match_beh_mon : monotone2 _match_beh.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
  Qed.

End Beh.
Hint Constructors _match_beh.
Hint Unfold match_beh.
Hint Resolve match_beh_mon: paco.







Definition improves2 {L0 L1} (st_src0: L0.(STS.state)) (st_tgt0: L1.(Smallstep.state)): Prop :=
  forall tr_tgt (BEH: state_behaves L1 st_tgt0 tr_tgt),
  exists tr_src, (<<BEH: (Beh.of_state L0 st_src0) tr_src>>) /\
                 (<<SIM: match_beh tr_tgt tr_src>>)
.

Definition improves2_program (L0: STS.semantics) (L1: Smallstep.semantics) : Prop :=
  forall tr_tgt (BEH: program_behaves L1 tr_tgt),
  exists tr_src, (<<BEH: (Beh.of_state L0 L0.(initial_state)) tr_src>>) /\
                 (<<SIM: match_beh tr_tgt tr_src>>)
.

Definition improves (L0 L1: STS.semantics): Prop :=
  Beh.improves (Beh.of_program L0) (Beh.of_program L1)
.

Lemma improves_combine: forall (S I: STS.semantics) (A: Smallstep.semantics),
    improves S I -> improves2_program I A -> improves2_program S A.
Proof.
  i. ii. exploit H0; et. i; des. exists tr_src. esplits; et. eapply H; et.
Qed.





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

Lemma squeeze_app X (l0 l1: list (option X))
  :
    squeeze (l0 ++ l1) =
    let '(l0', b0) := squeeze l0 in
    if b0
    then let '(l1', b1) := squeeze l1 in (l0'++l1', b1)
    else (l0', false).
Proof.
  revert l1. induction l0; ss.
  { i. des_ifs. }
  { i. des_ifs.
    { rewrite IHl0 in Heq. rewrite Heq1 in *. clarify. }
    { rewrite IHl0 in Heq. clarify. }
  }
Qed.

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

Record wf_at (L: Smallstep.semantics) (s:L.(Smallstep.state)) : Prop :=
  Wf_at {
      wf_at_determ:
        forall s1 t2 s2
               (STEP0: Step L s E0 s1)
               (STEP1 :Step L s t2 s2),
          (<<EQ: s1 = s2 /\ t2 = E0>>);
      wf_at_final:
        forall tr s' retv
               (FINAL: Smallstep.final_state L s retv)
               (STEP: Step L s tr s'),
          False;
      wf_at_final_determ:
        forall retv0 retv1
               (FINAL0: Smallstep.final_state L s retv0)
               (FINAL1: Smallstep.final_state L s retv1),
          (<<EQ: retv0 = retv1>>);
    }.

Definition wf_semantics (L: Smallstep.semantics) : Prop :=
  forall st, wf_at L st.

(* Record strict_determinate_at (L: Smallstep.semantics) (s:L.(Smallstep.state)) : Prop := *)
(*   Strict_determinate_at { *)
(*       ssd_determ_at: forall t1 s1 t2 s2 *)
(*         (STEP0: Step L s t1 s1) *)
(*         (STEP1 :Step L s t2 s2), *)
(*         <<EQ: s1 = s2>>; *)
(*     ssd_determ_at_final: forall tr s' retv *)
(*         (FINAL: Smallstep.final_state L s retv) *)
(*         (STEP: Step L s tr s'), *)
(*         False; *)
(*     ssd_traces_at: *)
(*       single_events_at L s *)
(*   }. *)

(************************ Src Aux ****************************)
(************************ Src Aux ****************************)
(************************ Src Aux ****************************)



Definition wf (L: semantics) (st0: L.(state)): Prop :=
  forall (ANG: L.(state_sort) st0 = angelic),
  forall st1 st1' (STEP: step L st0 None st1) (STEP: step L st0 None st1'), st1 = st1'
.



Section STAR.
  Variable L: semantics.
  Variable P: L.(state) -> Prop.
  Inductive pstar: L.(state) -> list event -> L.(state) -> Prop :=
  | star_refl: forall st_src0, pstar st_src0 [] st_src0
  | star_step: forall
      st_src0 es0 st_src1 es1 st_src2
      (P: P st_src0)
      (HD: step L st_src0 es0 st_src1)
      (TL: pstar st_src1 es1 st_src2)
    ,
      pstar st_src0 (es0 ++ es1) st_src2
  .
End STAR.
Hint Constructors pstar.
Definition dstar L := pstar L (fun st_src0 => L.(state_sort) st_src0 = demonic).
Definition star L := pstar L (wf L).

Lemma star_trans
      L
      st0 st1 st2 es0 es1
      (STEPS0: star L st0 es0 st1)
      (STEPS1: star L st1 es1 st2)
  :
    star L st0 (es0 ++ es1) st2.
Proof.
  revert es1 st2 STEPS1. induction STEPS0; et.
  i. rewrite <- List.app_assoc.
  econs; et. eapply IHSTEPS0. et.
Qed.

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
    econs; ss; et.
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

Lemma star_single_exact
      L0 st0 st3 e0
      (STAR: star L0 st0 [e0] st3)
  :
    exists st1 st2, (<<STAR: star L0 st0 [] st1>>) /\
                    (<<VIS: step L0 st1 (Some e0) st2>>) /\
                    (<<STAR: star L0 st2 [] st3>>)
.
Proof.
  dependent induction STAR; ii; ss.
  destruct es0; ss.
  { destruct es1; ss. clarify. esplits; et. econs. }
  clarify.
  exploit IHSTAR; et. i; des. esplits; try apply VIS; et.
  replace [] with ((@option_to_list event None) ++ []) by ss.
  econs; et.
Qed.

Definition NoStuck L (st_src0: state L): Prop :=
  L.(state_sort) st_src0 = angelic ->
  (<<NOSTUCK: exists ev st_src1, step L st_src0 ev st_src1>>)
(* (<<DTM: forall st_src1 st_src1', *)
(*     step L st_src0 None st_src1 -> *)
(*     step L st_src0 None st_src1' -> *)
(*     st_src1 = st_src1'>>) *)
.



(* Definition wf (L: semantics): Prop := *)
(*   forall (st0: L.(state)) (ANG: L.(state_sort) st0 = angelic), *)
(*   forall st1 st1' (STEP: step L st0 None st1) (STEP: step L st0 None st1'), st1 = st1' *)
(* . *)


Section BEH.

Variable L: semantics.
(* Hypothesis WFSRC: wf L. *)
(* Hypothesis WFSRC: forall st, (state_sort L st = angelic) -> wf L st. *)

(*** TODO: move to proper place? ***)
Lemma _beh_astep_rev
      r tr st0 ev st1
      (SRT: _.(state_sort) st0 = angelic)
      (WFSRC: wf _ st0)
      (STEP: _.(step) st0 ev st1)
      (BEH: paco2 (Beh._of_state L) r st1 tr)
  :
    <<BEH: paco2 (Beh._of_state L) r st0 tr>>
.
Proof.
  exploit wf_angelic; et. i; clarify.
  pfold. econsr; ss; et. rr. ii. exploit wf_angelic; et. i; des. subst.
  exploit WFSRC; [..|apply STEP|apply STEP0|]; ss. i; subst. esplits; et.
  punfold BEH.
Qed.

Lemma beh_of_state_star
      r st_src0 st_src1 es0 tr1
      (BEH: paco2 (Beh._of_state L) r st_src1 tr1)
      (STAR: star L st_src0 es0 st_src1)
  :
    <<BEH: paco2 (Beh._of_state L) r st_src0 (Tr.app es0 tr1)>>
.
Proof.
  revert BEH. revert tr1.
  induction STAR; ii; ss.
  exploit IHSTAR; et.
  intro U; des.
  destruct (state_sort L st_src0) eqn:T.
  - exploit wf_angelic; et. i; subst. ss.
    eapply _beh_astep_rev; et.
  - exploit wf_demonic; et. i; subst. ss.
    pfold. econs; ss; et. rr. esplits; ss; et. punfold U.
  - exploit wf_final; et. ss.
  - destruct es0; ss; cycle 1.
    { exploit wf_vis_event; et. ss. }
    pfold; econs; ss; et.
Qed.

Variant starC (r: (state L -> Tr.t -> Prop)): (state L -> Tr.t -> Prop) :=
| starC_intro
    st0 st1 tr
    (STAR: star L st0 [] st1)
    (SIM: r st1 tr)
  :
    starC r st0 tr
.

Hint Constructors starC: core.

Lemma starC_mon
      r1 r2
      (LE: r1 <2= r2)
  :
    starC r1 <2= starC r2
.
Proof. ii. destruct PR; econs; et. Qed.

Hint Resolve starC_mon: paco.

Lemma starC_prespectful: prespectful2 (Beh._of_state L) starC.
Proof.
  econs; eauto with paco.
  ii. rename x0 into st0. rename x1 into tr.
  inv PR. rename st2 into st1.
  apply GF in SIM.
  { change tr with (Tr.app [] tr). eapply beh_of_state_star; et. pfold.
    eapply Beh.of_state_mon; et.
  }
Qed.

Lemma starC_spec: starC <3= gupaco2 (Beh._of_state L) (cpn2 (Beh._of_state L)).
Proof. intros. eapply prespect2_uclo; eauto with paco. eapply starC_prespectful. Qed.

Variant starC2 (r: (state L -> Tr.t -> Prop)): (state L -> Tr.t -> Prop) :=
| starC2_intro
    st0 st1 tr0 tr1
    (STAR: star L st0 tr0 st1)
    (SIM: r st1 tr1)
  :
    starC2 r st0 (Tr.app tr0 tr1)
.

Hint Constructors starC2: core.

Lemma starC2_mon
      r1 r2
      (LE: r1 <2= r2)
  :
    starC2 r1 <2= starC2 r2
.
Proof. ii. destruct PR; econs; et. Qed.

Hint Resolve starC2_mon: paco.

Lemma starC2_prespectful: prespectful2 (Beh._of_state L) starC2.
Proof.
  econs; eauto with paco.
  ii. rename x0 into st0. rename x1 into tr.
  inv PR. rename st2 into st1.
  apply GF in SIM.
  { eapply beh_of_state_star; ss; et. pfold.
    eapply Beh.of_state_mon; et.
  }
Qed.

Lemma starC2_spec: starC2 <3= gupaco2 (Beh._of_state L) (cpn2 (Beh._of_state L)).
Proof. intros. eapply prespect2_uclo; eauto with paco. eapply starC2_prespectful. Qed.


End BEH.

(************************ Decompile ****************************)
(************************ Decompile ****************************)
(************************ Decompile ****************************)

Definition decompile_eval (ev: eventval): option Z :=
  match ev with
  | EVlong i => Some (Int64.signed i)
  | _ => None
  end
.

Definition decompile_event (ev: Events.event): option event :=
  match ev with
  | Event_syscall fn evs ev =>
    do vs <- sequence (List.map decompile_eval evs);
    do v <- decompile_eval ev;
    Some (event_sys fn vs↑ v↑)
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

Variant _Tr: Type :=
| _Tr_done (retv: Any.t)
| _Tr_spin
| _Tr_ub
| _Tr_nb
| _Tr_cons (hd: event) (tl: Tr.t)
.

Definition match_Tr (tr: Tr.t) :=
  match tr with
  | Tr.done retv => _Tr_done retv
  | Tr.spin => _Tr_spin
  | Tr.ub => _Tr_ub
  | Tr.nb => _Tr_nb
  | Tr.cons hd tl => _Tr_cons hd tl
  end.

Lemma Tr_eta (tr0 tr1: Tr.t)
      (EQ: match_Tr tr0 = match_Tr tr1)
  :
    tr0 = tr1.
Proof.
  destruct tr0, tr1; ss; clarify.
Qed.

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
  destruct tr. eapply Tr_eta. ss.
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
    Tr.app es (if succ then (Tr.done (Int.unsigned i)↑) else Tr.ub)
  | Diverges tr =>
    let '(es, succ) := squeeze (List.map decompile_event tr) in
    Tr.app es (if succ then (Tr.spin) else Tr.ub)
  | Reacts tr => (decompile_trinf tr)
  | Goes_wrong tr =>
    let '(es, succ) := squeeze (List.map decompile_event tr) in
    Tr.app es Tr.ub
  end
.

Lemma decompile_match_val v0 v1
      (SEQ: decompile_eval v0 = Some v1)
  :
    match_val v0 v1.
Proof.
  unfold decompile_eval in *. des_ifs.
Qed.

Lemma decompile_match_vals l0 l1
      (SEQ: sequence (List.map decompile_eval l0) = Some l1)
  :
    Forall2 match_val l0 l1.
Proof.
  revert l1 SEQ. induction l0; ss.
  { i. clarify. }
  { i. uo. des_ifs. econs; et.
    eapply decompile_match_val; et. }
Qed.

Lemma decompile_match_event
      e0 e1
      (D: decompile_event e0 = Some e1)
  :
    <<M: match_event e0 e1>>
.
Proof.
  destruct e0; ss. uo. des_ifs. econs.
  { eapply decompile_match_vals; et. }
  { eapply decompile_match_val; et. }
Qed.

Lemma match_val_iff v0 v1
  :
    decompile_eval v0 = Some v1 <->
    match_val v0 v1.
Proof.
  split.
  { eapply decompile_match_val. }
  i. inv H. ss.
Qed.

Lemma match_vals_iff l0 l1
  :
    sequence (List.map decompile_eval l0) = Some l1 <->
    Forall2 match_val l0 l1.
Proof.
  split.
  { eapply decompile_match_vals. }
  revert l1. induction l0; ss.
  { i. inv H. ss. }
  { i. inv H. hexploit IHl0; et. i.
    uo. rewrite H.
    eapply match_val_iff in H2. rewrite H2. ss. }
Qed.

Lemma match_event_iff
      e_src e_tgt
  :
    decompile_event e_tgt = Some e_src <->
    match_event e_tgt e_src
.
Proof.
  split.
  { eapply decompile_match_event. }
  i. inv H. ss. uo.
  eapply match_vals_iff in MV. rewrite MV.
  eapply match_val_iff in MV0. rewrite MV0. ss.
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
  revert es_tgt. induction es_src; ss.
  { i. split.
    { destruct es_tgt; ss. des_ifs. }
    { i. inv H. ss. }
  }
  { i. split.
    { i. destruct es_tgt; ss. des_ifs.
      hexploit IHes_src; et. i. econs.
      { eapply match_event_squeeze. ss. rewrite Heq. ss. }
      { eapply H. et. }
    }
    { i. inv H. eapply IHes_src in H4. ss.
      eapply match_event_iff in H3. rewrite H3.
      rewrite H4. ss.
    }
  }
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









Section SIM.

  Variable L0: STS.semantics.
  Variable L1: Smallstep.semantics.
  Let idx := Ord.t.
  Let ord := Ord.lt.

  Local Open Scope smallstep_scope.

  Variant _sim sim (i0: idx) (st_src0: L0.(STS.state)) (st_tgt0: L1.(Smallstep.state)): Prop :=
  | sim_fin
      retv
      (RANGE: (0 <= retv <= Int.max_unsigned)%Z)
      (* (RANGE: (Int.min_signed <= retv <= Int.max_signed)%Z) *)
      (SRT: _.(state_sort) st_src0 = final retv↑)
      (SRT: _.(Smallstep.final_state) st_tgt0 (Int.repr retv))
      (* (DTM: True) (*** TODO: copy-paste sd_final_determ in Smallstep.v ***) *)
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
      (DTM: forall st1 st2, (<<DTM1: _.(step) st_src0 None st1>>) -> (<<DTM2: _.(step) st_src0 None st2>>) -> st1 = st2)
      (SIM: forall st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src1 st_tgt0>>)
    :
      _sim sim i0 st_src0 st_tgt0


  | sim_demonic_both
      (SRT: _.(state_sort) st_src0 = demonic)
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


  Variant ordC (r: idx -> L0.(STS.state) -> L1.(Smallstep.state) -> Prop):
    idx -> L0.(STS.state) -> L1.(Smallstep.state) -> Prop :=
  | ordC_intro
      o0 o1 st_src st_tgt
      (ORD: Ord.le o0 o1)
      (SIM: r o0 st_src st_tgt)
    :
      ordC r o1 st_src st_tgt
  .

  Lemma ordC_mon
        r1 r2
        (LE: r1 <3= r2)
    :
      ordC r1 <3= ordC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve ordC_mon: paco.

  Lemma ordC_compatible: compatible3 (_sim) ordC.
  Proof.
    econs; eauto with paco.
    ii. inv PR. rename x0 into o1. rename x1 into st_src. rename x2 into st_tgt. inv SIM.
    - econs 1; eauto.
    - econs 2; eauto. i. hexploit SIM0; et. i. des. esplits; et. econs; [|et]. refl.
    - econs 3; eauto. des. esplits; et. { eapply Ord.lt_le_lt; et. } econs; et. refl.
    - econs 4; eauto. des. esplits; et. { eapply Ord.lt_le_lt; et. } econs; et. refl.
    - econs 5; eauto. i. hexploit SIM0; et. i. des. esplits; et.
      { eapply Ord.lt_le_lt; et. } econs; et. refl.
    - econs 6; eauto. des. esplits; et. econs; [|et]. refl.
  Qed.

  Lemma ordC_spec: ordC <4= gupaco3 (_sim) (cpn3 _sim).
  Proof.
    intros. gclo. econs.
    { eapply ordC_compatible. }
    eapply ordC_mon; [|et]. i. gbase. auto.
  Qed.

  Record simulation: Prop := mk_simulation {
    sim_init: forall st_tgt0 (INITT: L1.(Smallstep.initial_state) st_tgt0),
        exists i0, (<<SIM: sim i0 L0.(initial_state) st_tgt0>>);
    (* sim_init: exists i0 st_tgt0, (<<SIM: sim i0 L0.(initial_state) st_tgt0>>) /\ *)
    (*                              (<<INITT: L1.(Smallstep.initial_state) st_tgt0>>); *)
    (* sim_dtm: True; *)
  }
  .

  Hypothesis WF: well_founded ord.
  Hypothesis WFSEM: wf_semantics L1.

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
    { f_equal. clear - MV MV1. ginduction MV; ii; ss.
      { inv MV1; ss. }
      inv MV1; ss.
      f_equal; et.
      eapply match_val_inj; et.
    }
    f_equal. eapply match_val_inj; et.
  Qed.

  Lemma safe_along_events_step_some
        st_src0 st_src1 e_src e0 es0
        (WFSRC: wf L0 st_src0)
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
    { ss. }
  Qed.

  Lemma safe_along_events_step_none
        st_src0 st_src1 es0
        (WFSRC: wf L0 st_src0)
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
    revert st_src0 st_src1 es0_src es1 STAR MB SAFE. induction es0; ss.
    { i. clarify. ii. subst. exploit SAFE; [..|et|et].
      { instantiate (1:=tx_src).
        change tx_src with ([] ++ tx_src). eapply star_trans; et. }
      { et. }
      { et. }
    }
    { i. des_ifs. ii. subst. exploit SAFE; [..|et|et].
      { instantiate (1:=_ ++ _). eapply star_trans; et. }
      { instantiate (1:=a :: es0 ++ tx). ss. rewrite Heq.
        rewrite List.map_app. rewrite squeeze_app.
        rewrite MB. des_ifs. }
      { instantiate (1:=ty). ss. rewrite ! List.app_assoc. auto. }
    }
  Qed.

  (* Hypothesis WFSRC: wf L0. *)

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
    revert SAFE. revert SIM. depgen st_src0. revert i0.
    induction STEP; ii; ss.
    { esplits; et. econs; ss. }
    subst. rename s1 into st_tgt0. rename s2 into st_tgt1. rename s3 into st_tgt2.
    rename t1 into tr_tgt0. rename t2 into tr_tgt1.

    revert_until i0. pattern i0. eapply well_founded_ind; et. clear i0. intros i0 IH. i.

    punfold SIM. inv SIM.
    - (* fin *)
      exploit wf_at_final; [apply WFSEM|..]; et. ss.
    - (* vis *)
      clear SRT0. exploit SIM0; et. i; des. pclearbot.
      inv MATCH; ss. inv H4; ss. rename H3 into MB. eapply match_event_iff in MB. des_ifs.
      exploit IHSTEP; et.
      { eapply safe_along_events_step_some; et. unfold wf. i. rewrite ANG in SRT. ss. }
      i; des. clarify.
      esplits; et. rewrite cons_app.
      change [ev_src] with (option_to_list (Some ev_src)).
      econs; et.
      unfold wf. i. rewrite ANG in SRT. ss.
    - (* dsrc *)
      des. pclearbot. exploit IH; et.
      { eapply safe_along_events_step_none; et. unfold wf. i. rewrite ANG in SRT. ss. }
      i; des.
      esplits; et.
      rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. rewrite ANG in SRT. ss. 
    - (* dtgt *)
      des. pclearbot. exploit wf_at_determ;[apply WFSEM|apply STEP0|apply H|]. i; des. subst.
      exploit IHSTEP; et.
    - (* asrc *)
      exploit SAFE; try apply SRT.
      { econs; et. }
      { instantiate (1:=[]). ss. }
      { ss. }
      i; des.
      exploit wf_angelic; et. i; subst.
      exploit SIM0; et. i; des. pclearbot.
      exploit IH; et.
      { eapply safe_along_events_step_none; et. unfold wf. i. apply DTM; eauto. }
      i; des.
      esplits; et.
      rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. apply DTM; eauto.
    - (* dboth *)
      des. pclearbot.
      exploit wf_at_determ;[apply WFSEM|apply STEP0|apply H|]. i; des. subst.
      exploit IHSTEP; et.
      { eapply safe_along_events_step_none; et. unfold wf. i. rewrite ANG in SRT. ss. }
      i; des.
      esplits; et. rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. rewrite ANG in SRT. ss.
  Qed.

  Lemma sim_forever_silent
        i st_src st_tgt
        (SIM: sim i st_src st_tgt)
        (SILENT: Forever_silent L1 st_tgt)
    :
      Beh.state_spin L0 st_src.
  Proof.
    revert i st_src st_tgt SIM SILENT. pcofix CIH.
    intros i. induction (WF i). rename x into i. rename H0 into IH. clear H.
    i. inv SILENT. punfold SIM. inv SIM.
    { exploit wf_at_final; [apply WFSEM|..]; et. ss. }
    { des. hexploit wf_at_determ; [apply WFSEM|apply H|apply SRT0|]. i. des. clarify. }
    { des. inv SIM; ss. pfold. econs 2; et. esplits; et. right.
      eapply CIH; et. econs; et. }
    { des. inv SIM; ss. eapply IH; et.
      hexploit wf_at_determ; [apply WFSEM|apply STEP|apply H|]. i. des. clarify. }
    { pfold. econs 1; et. i.
      hexploit wf_angelic; et. i. subst.
      hexploit SIM0; et. i. des. inv SIM; ss. right. eapply CIH; et. econs; et. }
    { pfold. des. inv SIM; ss.
      hexploit wf_at_determ; [apply WFSEM|apply STEP|apply H|]. i. des. clarify.
      econs 2; et. esplits; et. }
  Qed.

  Lemma sim_goes_wrong
        i st_src st_tgt
        (SIM: sim i st_src st_tgt)
        (NOSTEP: Nostep L1 st_tgt)
        (NOFINAL: forall r, ~ L1.(Smallstep.final_state) st_tgt r)
    :
      Beh.of_state L0 st_src Tr.ub.
  Proof.
    ginit.
    { eapply cpn2_wcompat. eapply Beh.of_state_mon. }
    revert st_src st_tgt SIM NOSTEP NOFINAL.
    induction (WF i). rename x into i. rename H0 into IH. clear H.
    i. punfold SIM. inv SIM; ss.
    { exfalso. eapply NOFINAL; et. }
    { des. exfalso. eapply NOSTEP; et. }
    { des. inv SIM; ss.
      guclo starC_spec. econs.
      { instantiate (1:=st_src1).
        change ([]: list event) with (None ++ []: list event). econs; et.
        unfold wf; i. rewrite ANG in SRT; ss.
      }
      { eapply IH; et. }
    }
    { des. exfalso. eapply NOSTEP; et. }
    { destruct (classic (exists ev st_src1, step L0 st_src ev st_src1)).
      { des. exploit wf_angelic; et. i; subst. exploit SIM0; et. i; des. inv SIM; ss.
      guclo starC_spec. econs.
      { instantiate (1:=st_src1).
        change ([]: list event) with (None ++ []: list event). econs; et.
        unfold wf; i. eapply DTM; eauto.
      }
      { eapply IH; et. }
      }
      { gstep. econs 6; et. ii. exfalso. eapply H. et. }
    }
    { des. exfalso. eapply NOSTEP; et. }
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
          cut (Beh.of_state L0 st_src1 (Tr.done (Int.unsigned r)↑)); ss.
          (* assert(SAFE0: safe_along_trace st_src1 (Terminates tr r)). *)
          assert(SAFE0: safe_along_events st_src1 []).
          { clear - SAFE STEP MB.
            r in SAFE. specialize (SAFE tr).
            hexploit1 SAFE.
            { eexists (Terminates nil _). ss. unfold Eapp. rewrite List.app_nil_r. ss. }
            eapply safe_along_events_star; et.
            rewrite List.app_nil_r. ss.
          }
          clear - SAFE0 FIN WF SIM0 WFSEM.
          revert_until i1. pattern i1. eapply well_founded_ind; et. clear i1. intros i0 IH.
          i. punfold SIM0. inv SIM0.
          * pfold. econs; ss; et.
            exploit wf_at_final_determ; [eapply WFSEM|eapply SRT0|eapply FIN|].
            i. des. clarify.
            rewrite SRT. rewrite Int.unsigned_repr; auto.
          * des. exploit wf_at_final; [apply WFSEM|..]; et. ss.
          * des. pclearbot.
            exploit IH; et.
            { eapply safe_along_events_step_none; et. unfold wf; i. rewrite ANG in SRT; ss. }
            intro U.
            eapply Beh.beh_dstep; ss; et.
          * des. exploit wf_at_final; [apply WFSEM|..]; et. ss.
          * destruct (classic (exists ev st_src2, step L0 st_src1 ev st_src2)).
            { des. exploit wf_angelic; et. i; subst. exploit SIM; et. i; des.
              pclearbot.
              exploit IH; et.
              { eapply safe_along_events_step_none; et. unfold wf; i. eapply DTM; eauto. }
              i; des.
              eapply _beh_astep_rev; ss; et. unfold wf; i. eapply DTM; eauto. }
            contradict H. eapply SAFE0; et.
            { econs; ss; et. }
            { instantiate (1:=[]). ss. }
            { esplits; ss. }
          * des. exploit wf_at_final; [apply WFSEM|..]; et. ss.
        + ss. clear.
          induction tr; ii; ss.
          { pfold. econs; ss; et. }
          destruct (decompile_event a) eqn:T.
          * des_ifs_safe.
            eapply match_beh_cons; ss.
            { instantiate (1:=Terminates tr r). instantiate (1:=a). ss. }
            { ss. }
            { eapply decompile_match_event; ss. }
          * des_ifs_safe. ss. pfold; econsr; et; ss. r. esplits; et.
            rewrite behavior_app_E0; et.

      - (* diverge *)
        (rename t into tr).
        esplits; et.
        + rename H0 into BEH. ss.
          ginit. { eapply cpn2_wcompat; eauto with paco. } revert_until WFSEM. gcofix CIH. i.
          inv BEH.
          rename s2 into st_tgt1. rename tr into tr_tgt. rename H into STAR.
          hexploit simulation_star; try apply STAR; et.
          { eapply SAFE. exists (Diverges []). ss. rewrite E0_right. auto. }
          i; des.
          rewrite MB.
          guclo starC2_spec. econs; et.
          gfinal. right. pfold. econs 2.
          eapply sim_forever_silent; et. econs; et.
        + ss. clear.
          induction tr; ii; ss.
          { pfold. econs 2; ss; et. }
          destruct (decompile_event a) eqn:T.
          * des_ifs_safe.
            eapply match_beh_cons; ss.
            { instantiate (1:=Diverges tr). instantiate (1:=a). ss. }
            { ss. }
            { eapply decompile_match_event; ss. }
          * des_ifs_safe. ss. pfold; econsr; et; ss. r. esplits; et.
            rewrite behavior_app_E0; et.

      - (* forever_reactive *)
        (rename T into tr).
        esplits; et.
        + rename H into BEH. ss.
          ginit. { eapply cpn2_wcompat; eauto with paco. } revert_until WFSEM. gcofix CIH. i.
          (* revert_until WFSRC. pcofix CIH. i. *)
          inv BEH.
          rename s2 into st_tgt1. rename t into tr_tgt. rename H into STAR.
          hexploit simulation_star; try apply STAR; et.
          { eapply SAFE. exists (Reacts T). ss. }
          i; des.

          erewrite decompile_trinf_app; et.

          exploit CIH; et.
          { clear - SAFE MB STEP. r. i. eapply safe_along_events_star; et.
            eapply SAFE. r in BEH. des. r. exists beh'. rewrite behavior_app_assoc.
            rewrite <- BEH. ss. }
          intro KNOWLEDGE.
          assert(PROG: tr_src <> []).
          { ii; subst; ss. destruct tr_tgt; ss. des_ifs. }
          clear - KNOWLEDGE PROG STEP.
          induction STEP using star_event_ind; ss.
          clear_tac. spc IHSTEP1.
          eapply star_single_exact in STEP1. des.
          guclo starC_spec. econs; et.
          gstep. econs; et.
          { destruct (state_sort L0 st3) eqn:SORT; auto.
            - exfalso. hexploit wf_angelic; et; ss.
            - exfalso. hexploit wf_demonic; et; ss.
            - exfalso. hexploit wf_final; et; ss.
          }
          guclo starC_spec. econs; et.
          destruct es; ss.
          * guclo starC_spec. econs; et. gbase. et.
          * exploit IHSTEP1; ss; et. intro U. eapply gpaco2_mon; et. ii; ss.
        + eapply decompile_trinf_spec.

      - (* goes wrong *)
        (rename t into tr).
        esplits; et.
        + rename H0 into BEH. ss.
          ginit. { eapply cpn2_wcompat; eauto with paco. } revert_until WFSEM. gcofix CIH. i.
          hexploit simulation_star; try apply STAR; et.
          { eapply SAFE. exists (Goes_wrong []). ss. rewrite E0_right. auto. }
          i; des.
          rewrite MB.
          guclo starC2_spec. econs; et.
          gfinal. right. eapply paco2_mon.
          { eapply sim_goes_wrong; et. }
          { ss. }
        + ss. clear.
          induction tr; ii; ss.
          { pfold. econs 4; ss; et. ss. exists (Goes_wrong []). ss. }
          destruct (decompile_event a) eqn:T.
          * des_ifs_safe.
            eapply match_beh_cons; ss.
            { instantiate (1:=Goes_wrong tr). instantiate (1:=a). ss. }
            { ss. }
            { eapply decompile_match_event; ss. }
          * des_ifs_safe. ss. pfold; econsr; et; ss. r. esplits; et.
            rewrite behavior_app_E0; et.
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
      - clear - STAR STUCK.
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
