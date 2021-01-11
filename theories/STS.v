Require Import sflib.
Require Import Universe.

Set Implicit Arguments.



Inductive sort: Type :=
| angelic
| demonic
| final (retv: Z)
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

