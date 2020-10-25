Require Import sflib.
Require Import Universe.
Require Import Semantics.
From Paco Require Import paco.
Require Import RelationClasses List.
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
(* Require Import Streams. *)

Ltac et := eauto.

Module Beh.
  CoInductive t: Type :=
  | done
  | spin
  | cons (hd: event) (tl: t)
  .
  Infix "##" := cons (at level 60, right associativity).
  (*** past -------------> future ***)
  (*** a ## b ## c ## spin / done ***)

  (*** le src tgt ***)
  Inductive _le (le: t -> t -> Prop): t -> t -> Prop :=
  | le_done
    :
      _le le (done) (done)
  | le_ub
      tl beh
    :
      _le le (event_ub ## tl) beh
  | le_nb
      tl beh
    :
      _le le beh (event_nb ## tl)
  | le_step
      ev tl0 tl1
      (TL: le tl0 tl1)
    :
      _le le (ev ## tl0) (ev ## tl1)
  .

  Definition le: _ -> _ -> Prop := paco2 _le bot2.

  Lemma le_mon: monotone2 _le.
  Proof.
    ii. inv IN; econs; eauto.
  Qed.

  Hint Constructors _le.
  Hint Unfold le.
  Hint Resolve le_mon: paco.

  Remark ub_test ev: le (event_ub ## done) (ev ## done). pfold. econs; eauto. Qed.
  Remark ub_prefix s0: ~ le ((event_sys s0) ## event_ub ## done) done. ii. punfold H. inv H. Qed.

End Beh.



Section BEHAVES.

Variable L: semantics.

Definition union (st0: L.(state)) (P: (option event) -> L.(state) -> Prop) :=
  exists ev st1, <<STEP: L.(step) st0 ev st1>> /\ <<UNION: P ev st1>>.
Definition inter (st0: L.(state)) (P: (option event) -> L.(state) -> Prop) :=
  forall ev st1 (STEP: L.(step) st0 ev st1), <<INTER: P ev st1>>.

Inductive _state_behaves (state_behaves: L.(state) -> Beh.t -> Prop)
          (st0: L.(state)): Beh.t -> Prop :=
| sb_final
    (FINAL: L.(state_sort) st0 = final)
  :
    _state_behaves state_behaves st0 (Beh.done)
| sb_angelic
    ev evs
    (ANG: L.(state_sort) st0 = angelic)
    (STEP: inter st0 (fun e st1 => <<TL: state_behaves st1 evs>> /\ <<HD: e = Some ev>>))
  :
    _state_behaves state_behaves st0 (Beh.cons ev evs)
| sb_demonic
    ev evs
    (DEM: L.(state_sort) st0 = demonic)
    (STEP: union st0 (fun e st1 => <<TL: state_behaves st1 evs>> /\ <<HD: e = Some ev>>))
  :
    _state_behaves state_behaves st0 (Beh.cons ev evs)
| sb_angelic_spin
    (ANG: L.(state_sort) st0 = angelic)
    (STEP: inter st0 (fun e st1 => <<TL: state_behaves st1 Beh.spin>> /\ <<HD: e = None>>))
  :
    _state_behaves state_behaves st0 Beh.spin 
| sb_demonic_spin
    (ANG: L.(state_sort) st0 = demonic)
    (STEP: union st0 (fun e st1 => <<TL: state_behaves st1 Beh.spin>> /\ <<HD: e = None>>))
  :
    _state_behaves state_behaves st0 Beh.spin 
.

Definition state_behaves: _ -> _ -> Prop := paco2 _state_behaves bot2.

Lemma state_behaves_mon: monotone2 _state_behaves.
Proof.
  ii. inv IN.
  - econs; eauto.
  - econs 2; eauto. ii. exploit STEP; et. i; des. eauto.
  - econs 3; eauto. rr in STEP. des. rr. esplits; eauto.
  - econs 4; eauto. ii. exploit STEP; et. i; des. eauto.
  - econs 5; eauto. rr in STEP. des. rr. esplits; eauto.
Qed.

Hint Constructors _state_behaves.
Hint Unfold state_behaves.
Hint Resolve state_behaves_mon: paco.

Definition program_behaves: behavior -> Prop := state_behaves L.(initial_state).

End BEHAVES.
