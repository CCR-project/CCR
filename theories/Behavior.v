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
  | ub
  | nb
  | cons (hd: syscall) (tl: t)
  .
  Infix "##" := cons (at level 60, right associativity).
  (*** past -------------> future ***)
  (*** a ## b ## c ## spin / done ***)

  Inductive fin: Type :=
  | fdone
  | fspin
  | fub
  | fnb
  | fcons (hd: syscall) (tl: fin)
  .

  Fixpoint embed (bh: fin): t :=
    match bh with
    | fdone => done
    | fspin => spin
    | fub => ub
    | fnb => nb
    | fcons hd tl => cons hd (embed tl)
    end
  .

  (*** le src tgt ***)
  Inductive _le (le: t -> t -> Prop): t -> t -> Prop :=
  | le_done
    :
      _le le (done) (done)
  | le_spin
    :
      _le le spin spin 
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

End Beh.



Section BEHAVES.

Variable L: semantics.

Definition union (st0: L.(state)) (P: (option event) -> L.(state) -> Prop) :=
  exists ev st1, <<STEP: L.(step) st0 ev st1>> /\ <<UNION: P ev st1>>.
Definition inter (st0: L.(state)) (P: (option event) -> L.(state) -> Prop) :=
  forall ev st1 (STEP: L.(step) st0 ev st1), <<INTER: P ev st1>>.

Inductive _state_spin (state_spin: L.(state) -> Prop)
  (st0: L.(state)): Prop :=
| state_spin_angelic
    (ANG: L.(state_sort) st0 = angelic)
    (STEP: forall ev st1 (STEP: L.(step) st0 ev st1), <<HD: ev = None>> /\ <<TL: state_spin st1>>)
| state_spin_demonic
    (DEM: L.(state_sort) st0 = demonic)
    (STEP: exists ev st1, <<STEP: L.(step) st0 ev st1>> /\ <<HD: ev = None>> /\ <<TL: state_spin st1>>)
.

Definition state_spin: _ -> Prop := paco1 _state_spin bot1.

Lemma state_spin_mon: monotone1 _state_spin.
Proof.
  ii. inv IN; try (by econs; eauto).
  - econs 1; et. ii. exploit STEP; et. i; des. et.
  - des. econs 2; et. esplits; et.
Qed.

Hint Constructors _state_spin.
Hint Unfold state_spin.
Hint Resolve state_spin_mon: paco.



Inductive _state_behaves (state_behaves: L.(state) -> Beh.t -> Prop)
          (st0: L.(state)): Beh.t -> Prop :=
| sb_final
    (FINAL: L.(state_sort) st0 = final)
  :
    _state_behaves state_behaves st0 (Beh.done)
| sb_spin
    (SPIN: state_spin st0)
  :
    _state_behaves state_behaves st0 (Beh.spin)
| sb_ub
    (UB: ~exists ev st1, L.(step) st0 ev st1)
  :
    _state_behaves state_behaves st0 (Beh.ub)
| sb_nb
  :
    _state_behaves state_behaves st0 (Beh.nb)
| sb_angelic_tau
    evs
    (ANG: L.(state_sort) st0 = angelic)
    (STEP: inter st0 (fun e st1 => (<<TL: _state_behaves state_behaves st1 evs>>) /\ (<<HD: e = None>>)))
  :
    _state_behaves state_behaves st0 evs 
| sb_demonic_tau
    evs
    (DEM: L.(state_sort) st0 = demonic)
    (STEP: union st0 (fun e st1 => (<<TL: _state_behaves state_behaves st1 evs>>) /\ (<<HD: e = None>>)))
  :
    _state_behaves state_behaves st0 evs
| sb_angelic_sys
    ev evs
    (ANG: L.(state_sort) st0 = angelic)
    (STEP: inter st0 (fun e st1 => (<<TL: state_behaves st1 evs>>) /\ (<<HD: e = Some (event_sys ev)>>)))
  :
    _state_behaves state_behaves st0 (Beh.cons ev evs)
| sb_demonic_sys
    ev evs
    (DEM: L.(state_sort) st0 = demonic)
    (STEP: union st0 (fun e st1 => (<<TL: state_behaves st1 evs>>) /\ (<<HD: e = Some (event_sys ev)>>)))
  :
    _state_behaves state_behaves st0 (Beh.cons ev evs)
.
(*** TODO: ub / nb / spin ***)

Theorem state_behaves_ind:
forall (state_behaves : state L -> Beh.t -> Prop) (st0 : state L) (P : Beh.t -> Prop),
(state_sort L st0 = final -> P Beh.done) ->
(state_spin st0 -> P Beh.spin) ->
(forall (evs: Beh.t) (IH: True),
 state_sort L st0 = angelic ->
 inter st0
   (fun (e : option event) (st1 : state L) =>
    <<TL: _state_behaves state_behaves st1 evs >> /\ <<HD: e = None >>) -> P evs) ->
(forall (evs: Beh.t) (IH: True),
 state_sort L st0 = demonic ->
 union st0
   (fun (e : option event) (st1 : state L) =>
    <<TL: _state_behaves state_behaves st1 evs >> /\ <<HD: e = None >>) -> P evs) ->
(forall (ev : syscall) (evs : Beh.t) (IHH: True),
 state_sort L st0 = angelic ->
 inter st0
   (fun (e : option event) (st1 : state L) =>
    <<TL: state_behaves st1 evs >> /\ <<HD: e = Some (event_sys ev) >>) -> P (Beh.cons ev evs)) ->
(forall (ev : syscall) (evs : Beh.t) (IHH: True),
 state_sort L st0 = demonic ->
 union st0
   (fun (e : option event) (st1 : state L) =>
    <<TL: state_behaves st1 evs >> /\ <<HD: e = Some (event_sys ev) >>) -> P (Beh.cons ev evs)) ->
forall t : Beh.t, _state_behaves state_behaves st0 t -> P t
.
Proof.
  (* { i. inv H5; eauto. } *)
  i. generalize dependent t. fix IH 2.
  i. inv H5; eauto.
Admitted.

Definition state_behaves: _ -> _ -> Prop := paco2 _state_behaves bot2.

Lemma state_behaves_mon: monotone2 _state_behaves.
Proof.
  {
    rr. fix IH 5. i.
    inv IN.
    - econs 1; et.
    - econs 2; et.
    - econs 3; et.
    - econs 4; et.
    - econs 5; et. ii. exploit STEP; et. i; des. clarify. esplits; et.
    - rr in STEP. des. econs 6; et. rr. esplits; et.
    - econs 7; et. ii. exploit STEP; et. i; des. clarify. esplits; et.
    - rr in STEP. des. econs 8; et. rr. esplits; et.
  }
Qed.

Hint Constructors _state_behaves.
Hint Unfold state_behaves.
Hint Resolve state_behaves_mon: paco.

Definition program_behaves: Beh.t -> Prop := state_behaves L.(initial_state).

End BEHAVES.

Lemma prefix_closed
      L
  :
    <<NB: program_behaves L Beh.nb>>
.
Proof. pfold. econs; et. Qed.

Lemma nb_bottom
      L
  :
    <<NB: program_behaves L Beh.nb>>
.
Proof. pfold. econs; et. Qed.
