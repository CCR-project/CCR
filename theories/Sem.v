Require Import sflib.
Require Import Universe.

Set Implicit Arguments.



Inductive sort: Type :=
| angelic
| demonic
| final
| vis
.

Record semantics : Type := Semantics_gen {
  state: Type;
  step : state -> option event -> state -> Prop;
  initial_state: state;
  state_sort: state -> sort;
  (* wf_vis: forall st0 (VIS: state_sort st0 = vis), exists ! ev st1, step st0 (Some ev) st1; *)
  (* wf_vis: forall st0 (VIS: state_sort st0 = vis), exists ev st1, step st0 (Some ev) st1; *)
  wf_vis: forall
      st0 ev0 ev1 st1 st2
      (VIS: state_sort st0 = vis)
      (STEP: step st0 ev0 st1)
      (STEP: step st0 ev1 st2)
    ,
      ev0 = ev1 /\ st1 = st2;
  wf_angelic: forall st0 ev st1 (VIS: state_sort st0 = angelic) (STEP: step st0 ev st1), ev = None;
  wf_demonic: forall st0 ev st1 (VIS: state_sort st0 = demonic) (STEP: step st0 ev st1), ev = None;
}.

Section SEM.
Variable L: semantics.

Inductive tstar (st0: L.(state)) (P: L.(state) -> Prop): Prop :=
| tstar_refl
    (PROP: P st0)
  :
    tstar st0 P
| tstar_demonic
    (SRT: L.(state_sort) st0 = demonic)
    (STEP: exists st1 (STEP: L.(step) st0 None st1), <<TL: tstar st1 P>>)
  :
    tstar st0 P
| tstar_angelic
    (SRT: L.(state_sort) st0 = angelic)
    (STEP: forall st1 (STEP: L.(step) st0 None st1), <<TL: tstar st1 P>>)
  :
    tstar st0 P
.

Theorem tstar_ind2 :
forall P : state L -> (state L -> Prop) -> Prop,
(forall (st0 : state L) (P0 : state L -> Prop), P0 st0 -> P st0 P0) ->
(forall (st0 : state L) (P0 : state L -> Prop),
 state_sort L st0 = demonic ->
 (exists (st1 : state L) (_ : step L st0 None st1), <<TL: tstar st1 P0 >> /\ <<IH: P st1 P0>>) -> P st0 P0) ->
(forall (st0 : state L) (P0 : state L -> Prop),
 state_sort L st0 = angelic ->
 (forall st1 : state L, step L st0 None st1 -> <<TL: tstar st1 P0 >>) ->
 (forall st1 : state L, step L st0 None st1 -> P st1 P0) -> P st0 P0) ->
forall (st0 : state L) (P0 : state L -> Prop), tstar st0 P0 -> P st0 P0.
Proof.
  fix IH 7. i.
  inv H2.
  - eapply H; eauto.
  - eapply H0; eauto. des. esplits; eauto. eapply IH; eauto.
  - eapply H1; eauto. ii. exploit STEP; eauto. i. esplits; eauto. eapply IH; eauto.
Qed.

Definition is_leaf (st0: L.(state)): bool :=
  match L.(state_sort) st0 with
  | final | vis => true
  | _ => false
  end
.
End SEM.
