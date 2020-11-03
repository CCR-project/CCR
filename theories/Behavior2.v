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
  | nb
  | cons (hd: syscall) (tl: t)
  .
  Infix "##" := cons (at level 60, right associativity).
  (*** past -------------> future ***)
  (*** a ## b ## c ## spin / done ***)

  Fixpoint app (pre: list syscall) (bh: t): t :=
    match pre with
    | [] => bh
    | hd :: tl => cons hd (app tl bh)
    end
  .
  Lemma fold_app
        s pre tl
    :
      (Beh.cons s (Beh.app pre tl)) = Beh.app (s :: pre) tl
  .
  Proof. reflexivity. Qed.

  Definition prefix (pre: list syscall) (bh: t): Prop :=
    exists tl, <<APP: app pre tl = bh>>
  .

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



Inductive _state_behaves (state_behaves: L.(state) -> Beh.t -> Prop): L.(state) -> Beh.t -> Prop :=
| sb_final
    st0
    (FINAL: L.(state_sort) st0 = final)
  :
    _state_behaves state_behaves st0 (Beh.done)
| sb_spin
    st0
    (SPIN: state_spin st0)
  :
    _state_behaves state_behaves st0 (Beh.spin)
| sb_ub
    st0 beh
    (ERROR: L.(state_sort) st0 = error)
  :
    _state_behaves state_behaves st0 beh
| sb_nb
    st0
  :
    _state_behaves state_behaves st0 (Beh.nb)
(* | sb_demonic *)
(*     st0 *)
(*     evs *)
(*     (DEM: L.(state_sort) st0 = demonic) *)
(*     (STEP: union st0 (fun e st1 => *)
(*                         (<<TAU: (<<HD: e = None>>) /\ (<<TL: _state_behaves state_behaves st1 evs>>)>>) *)
(*                         \/ *)
(*                         (<<SYS: exists hd tl, (<<HD: e = Some (event_sys hd)>>) /\ *)
(*                                               (<<TL: state_behaves st1 tl>>) /\ *)
(*                                               (<<CONS: evs = Beh.cons hd tl>>)>>))) *)
(*   : *)
(*     _state_behaves state_behaves st0 evs *)
| sb_demonic_tau
    st0
    evs
    (DEM: L.(state_sort) st0 = demonic)
    (STEP: union st0 (fun e st1 => (<<HD: e = None>>) /\ (<<TL: _state_behaves state_behaves st1 evs>>)))
  :
    _state_behaves state_behaves st0 evs
| sb_demonic_sys
    st0
    ev evs
    (DEM: L.(state_sort) st0 = demonic)
    (STEP: union st0 (fun e st1 => (<<HD: e = Some (event_sys ev)>>) /\ (<<TL: state_behaves st1 evs>>)))
  :
    _state_behaves state_behaves st0 (Beh.cons ev evs)
| sb_angelic
    st0
    evs
    (ANG: L.(state_sort) st0 = angelic)
    (STEP: inter st0 (fun e st1 =>
                        (<<TAU: (<<HD: e = None>>) /\ (<<TL: _state_behaves state_behaves st1 evs>>)>>)
                        \/
                        (<<SYS: exists hd tl, (<<HD: e = Some (event_sys hd)>>) /\
                                              (<<TL: state_behaves st1 tl>>) /\
                                              (<<CONS: evs = Beh.cons hd tl>>)>>)))
  :
    _state_behaves state_behaves st0 evs
.

Definition state_behaves: _ -> _ -> Prop := paco2 _state_behaves bot2.

Theorem state_behaves_ind :
forall (r P: _ -> _ -> Prop),
(forall st0, state_sort L st0 = final -> P st0 Beh.done) ->
(forall st0, state_spin st0 -> P st0 Beh.spin) ->
(forall st0 beh, L.(state_sort) st0 = error -> P st0 beh) ->
(forall st0, P st0 Beh.nb) ->
(* (forall st0 evs (IH: exists st1 (STEP: L.(step) st0 None st1), P st1 evs) *)
(* (forall st0 evs (IH: exists st1, (<<STEP: L.(step) st0 None st1>>) /\ P st1 evs) *)
(* (forall st0 evs (IH: forall st1 (STEP: L.(step) st0 None st1), P st1 evs) *)

(* (forall st0 evs *)
(*  (DEM: state_sort L st0 = demonic) *)
(*  (STEP: union st0 *)
(*    (fun e st1 => *)
(*     <<TAU: <<HD: e = None >> /\ <<TL: _state_behaves r st1 evs >> /\ <<IH: P st1 evs>> >> \/ *)
(*     <<SYS: exists hd tl, *)
(*       <<HD: e = Some (event_sys hd) >> /\ <<TL: r st1 tl >> /\ *)
(*       <<CONS: evs = Beh.cons hd tl >> >>)), *)
(*     P st0 evs) -> *)

(forall st0 evs
        (* (IH: forall st1 (STEP: L.(step) st0 None st1), P st1 evs) *)
        (* (IH: exists st1 (STEP: L.(step) st0 None st1), P st1 evs) *)
 (DEM: state_sort L st0 = demonic)
 (STEP: union st0
   (fun e st1 =>
    <<HD: e = None >> /\ <<TL: _state_behaves r st1 evs >> /\ <<IH: P st1 evs>>)), P st0 evs) ->
(forall st0 ev evs
 (DEM: state_sort L st0 = demonic)
 (STEP: union st0
   (fun e st1 =>
      <<HD: e = Some (event_sys ev) >> /\ <<TL: r st1 evs >>)), P st0 (Beh.cons ev evs)) ->
(forall st0 evs
        (* (IH: forall st1 (STEP: L.(step) st0 None st1), P st1 evs) *)
 (ANG: state_sort L st0 = angelic)
 (STEP: inter st0
   (fun e st1 =>
    <<TAU: <<HD: e = None >> /\ <<TL: _state_behaves r st1 evs >> /\ <<IH: P st1 evs>> >> \/
    <<SYS:
    exists hd tl, <<HD: e = Some (event_sys hd) >> /\ <<TL: r st1 tl >> /\
                  <<CONS: evs = Beh.cons hd tl >> >>)),
 P st0 evs) ->
forall s t, _state_behaves r s t -> P s t.
Proof.
  (* fix IH 11. i. *)
  (* inv H5; eauto. *)
  (* - eapply H3; eauto. rr in STEP. des; clarify. *)
  (*   + esplits; eauto. rr. esplits; eauto. left. esplits; eauto. eapply IH; eauto. Guarded. *)
  (*   + esplits; eauto. rr. esplits; eauto. right. esplits; eauto. *)
  (* - eapply H4; eauto. ii. exploit STEP; eauto. i; des; clarify. *)
  (*   + esplits; eauto. left. esplits; eauto. eapply IH; eauto. *)
  (*   + esplits; eauto. right. esplits; eauto. *)
  fix IH 12. i.
  inv H6; eauto.
  - eapply H3; eauto. rr in STEP. des; clarify. esplits; eauto. rr. esplits; eauto. eapply IH; eauto.
  - eapply H5; eauto. ii. exploit STEP; eauto. i; des; clarify.
    + esplits; eauto. left. esplits; eauto. eapply IH; eauto.
    + esplits; eauto. right. esplits; eauto.
Qed.

Lemma state_behaves_mon: monotone2 _state_behaves.
Proof.
  ii. induction IN using state_behaves_ind; eauto.
  - econs 1; et.
  - econs 2; et.
  - econs 3; et.
  - econs 4; et.
  (* - econs 5; et. rr in STEP. des; clarify. *)
  (*   + rr. esplits; et. *)
  (*   + rr. esplits; et. right. esplits; et. *)
  (* - econs 6; et. ii. exploit STEP; eauto. i; des; clarify. *)
  (*   + esplits; et. *)
  (*   + esplits; et. right. esplits; et. *)
  - econs 5; et. rr in STEP. des; clarify. rr. esplits; et.
  - econs 6; et. rr in STEP. des; clarify. rr. esplits; et.
  - econs 7; et. ii. exploit STEP; eauto. i; des; clarify.
    + esplits; et.
    + esplits; et. right. esplits; et.
Qed.

Hint Constructors _state_behaves.
Hint Unfold state_behaves.
Hint Resolve state_behaves_mon: paco.

(**********************
TODO: CompCert랑 비교하고 이해: induction (star step)이 거기선 쉽고 왜 여기선 어려운가?
***********************)





Definition program_behaves: Beh.t -> Prop := state_behaves L.(initial_state).

End BEHAVES.
Hint Constructors _state_spin.
Hint Unfold state_spin.
Hint Resolve state_spin_mon: paco.
Hint Constructors _state_behaves.
Hint Unfold state_behaves.
Hint Resolve state_behaves_mon: paco.

Lemma prefix_closed_state
      L
      st0 pre bh
      (BEH: state_behaves L st0 bh)
      (PRE: Beh.prefix pre bh)
  :
    <<NB: state_behaves L st0 (Beh.app pre Beh.nb)>>
.
Proof.
  revert_until L. pcofix CIH. i. punfold BEH. rr in PRE. des; subst.
  destruct pre; ss; clarify.
  { pfold. econs 4; eauto. }
  inv BEH; ss; clarify.
  - pfold. econs 3; eauto.
  - pfold. econs 5; eauto. rr in STEP. des; clarify. rr. esplits; eauto.
    remember (Beh.cons s (Beh.app pre tl)) as tmp. revert Heqtmp.
    clear DEM STEP0 st0. revert pre s tl.
    induction TL using state_behaves_ind; ii; ss; clarify.
    + econs 3; eauto.
    + rr in STEP. des; clarify. econs 5; eauto. rr. esplits; eauto.
    + rr in STEP. des; clarify. pclearbot. econs 6; eauto. rr. esplits; eauto. right.
      eapply CIH; eauto. rr. eauto.
    + econs 7; eauto. ii. exploit STEP; eauto. i; des.
      * clarify. esplits; eauto.
      * clarify. esplits; eauto. right. esplits; swap 2 3; eauto. pclearbot. right. eapply CIH; eauto.
        rr; et.
  - pfold. econs 6; eauto. rr in STEP. des; clarify. rr. esplits; eauto. pclearbot. right.
    eapply CIH; try apply TL. rr. eauto.
  - pfold. econs 7; eauto. ii. exploit STEP; eauto. clear STEP. i; des; clarify.
    + esplits; eauto. left. esplits; eauto.
      remember (Beh.cons s (Beh.app pre tl)) as tmp. revert Heqtmp.
      clear ANG STEP0 st0. revert pre s tl.
      induction TL using state_behaves_ind; ii; ss; clarify.
      * econs 3; eauto.
      * rr in STEP. des; clarify. econs 5; eauto. rr. esplits; eauto.
      * rr in STEP. des; clarify. pclearbot. econs 6; eauto. rr. esplits; eauto. right.
        eapply CIH; eauto. rr. eauto.
      * econs 7; eauto. ii. exploit STEP; eauto. i; des.
        -- clarify. esplits; eauto.
        -- clarify. esplits; eauto. right. esplits; swap 2 3; eauto. pclearbot. right. eapply CIH; eauto.
           rr; et.
    + esplits; eauto. right. esplits; swap 2 3; eauto. pclearbot. right. eapply CIH; eauto. rr; et.
Qed.

Theorem prefix_closed
      L
      pre bh
      (BEH: program_behaves L bh)
      (PRE: Beh.prefix pre bh)
  :
    <<NB: program_behaves L (Beh.app pre Beh.nb)>>
.
Proof.
  eapply prefix_closed_state; eauto.
Qed.

Lemma nb_bottom
      L
  :
    <<NB: program_behaves L Beh.nb>>
.
Proof. pfold. econs 4; et. Qed.
