Require Import sflib.
Require Import Universe.

Inductive sort: Type :=
| angelic
| demonic
| final
.

Record semantics : Type := Semantics_gen {
  state: Type;
  step : state -> option event -> state -> Prop;
  initial_state: state;
  (* final_state: state -> Prop; *)
  state_sort: state -> sort;
}.
