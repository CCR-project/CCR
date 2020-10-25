Require Import sflib.

Class Universe := {
  event: Type;
  val: Type;
}
.

Context `{Universe}.

Record semantics : Type := Semantics_gen {
  state: Type;
  step : state -> event -> state -> Prop;
  initial_state: state -> Prop;
  final_state: state -> val -> Prop;
  is_angelic: state -> bool;
}.
