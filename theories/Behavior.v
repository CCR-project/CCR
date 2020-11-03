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

  (* Inductive fin: Type := *)
  (* | fdone *)
  (* | fspin *)
  (* | fub *)
  (* | fnb *)
  (* | fcons (hd: syscall) (tl: fin) *)
  (* . *)

  (* Fixpoint embed (bh: fin): t := *)
  (*   match bh with *)
  (*   | fdone => done *)
  (*   | fspin => spin *)
  (*   | fub => ub *)
  (*   | fnb => nb *)
  (*   | fcons hd tl => cons hd (embed tl) *)
  (*   end *)
  (* . *)

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
Hint Constructors Beh._le.
Hint Unfold Beh.le.
Hint Resolve Beh.le_mon: paco.



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
    st0
    (UB: ~exists ev st1, L.(step) st0 ev st1)
  :
    _state_behaves state_behaves st0 (Beh.ub)
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
(forall st0, ~ (exists ev st1, step L st0 ev st1) -> P st0 Beh.ub) ->
(forall st0, P st0 Beh.nb) ->
(* (forall st0 evs (IH: exists st1 (STEP: L.(step) st0 None st1), P st1 evs) *)
(* (forall st0 evs (IH: exists st1, (<<STEP: L.(step) st0 None st1>>) /\ P st1 evs) *)
(* (forall st0 evs (IH: forall st1 (STEP: L.(step) st0 None st1), P st1 evs) *)

(* (forall st0 evs (IH: forall _st1 (SAFE: L.(step) st0 None _st1), *)
(*                     exists st1, <<STEP: L.(step) st0 None st1>> /\ P st1 evs) *)
(*  (DEM: state_sort L st0 = demonic) *)
(*  (STEP: union st0 *)
(*    (fun e st1 => *)
(*     <<TAU: <<HD: e = None >> /\ <<TL: _state_behaves r st1 evs >> >> \/ *)
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
  fix IH 12. i.
  inv H6; eauto.
  - eapply H3; eauto. rr in STEP. des; clarify. esplits; eauto.
    rr. esplits; eauto. eapply IH; eauto. Guarded.
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
  - econs 5; et. rr in STEP. des. clarify. rr. esplits; et.
  - econs 6; et. rr in STEP. des. clarify. rr. esplits; et.
  - econs 7; et. ii. exploit STEP; eauto. i; des; clarify.
    + esplits; et.
    + esplits; et. right. esplits; et.
  - econs 1; et.
  assert(TRIAL1: monotone2 _state_behaves).
  {
    ii. revert IN. revert x1. revert x0. (* pattern x0. pattern x1. *)
    eapply _state_behaves_ind_max with (state_behaves := r); ii.
    - clear Q. econs 1; et.
    - clear Q. econs 2; et.
    - clear Q. econs 3; et.
    - clear Q. econs 4; et.
    - econs 5; et. ii. exploit STEP; et. i; des. clarify. esplits; et. admit.
    - rr in STEP. des. econs 6; et. rr. esplits; et. admit.
    - econs 7; et. ii. exploit STEP; et. i; des. clarify. esplits; et.
    - rr in STEP. des. econs 8; et. rr. esplits; et.
  }
  clear TRIAL1.
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
Admitted.

Hint Constructors _state_behaves.
Hint Unfold state_behaves.
Hint Resolve state_behaves_mon: paco.

Inductive _state_behaves' (state_behaves': nat -> L.(state) -> Beh.t -> Prop):
          nat -> L.(state) -> Beh.t -> Prop :=
| sbi_final
    st0 fuel
    (FINAL: L.(state_sort) st0 = final)
  :
    _state_behaves' state_behaves' fuel st0 (Beh.done)
| sbi_spin
    st0 fuel
    (SPIN: state_spin st0)
  :
    _state_behaves' state_behaves' fuel st0 (Beh.spin)
| sbi_ub
    st0 fuel
    (UB: ~exists ev st1, L.(step) st0 ev st1)
  :
    _state_behaves' state_behaves' fuel st0 (Beh.ub)
| sbi_nb
    st0 fuel
  :
    _state_behaves' state_behaves' fuel st0 (Beh.nb)
| sbi_angelic_tau
    st0 fuel
    evs
    (ANG: L.(state_sort) st0 = angelic)
    (STEP: inter st0 (fun e st1 => (<<TL: state_behaves' fuel st1 evs>>) /\ (<<HD: e = None>>)))
  :
    _state_behaves' state_behaves' (S fuel) st0 evs 
| sbi_demonic_tau
    st0 fuel
    evs
    (DEM: L.(state_sort) st0 = demonic)
    (STEP: union st0 (fun e st1 => (<<TL: state_behaves' fuel st1 evs>>) /\ (<<HD: e = None>>)))
  :
    _state_behaves' state_behaves' (S fuel) st0 evs
| sbi_angelic_sys
    st0 fuel
    ev evs
    (ANG: L.(state_sort) st0 = angelic)
    (STEP: inter st0 (fun e st1 => (<<TL: state_behaves' fuel st1 evs>>) /\ (<<HD: e = Some (event_sys ev)>>)))
  :
    _state_behaves' state_behaves' fuel st0 (Beh.cons ev evs)
| sbi_demonic_sys
    st0 fuel
    ev evs
    (DEM: L.(state_sort) st0 = demonic)
    (STEP: union st0 (fun e st1 => (<<TL: state_behaves' fuel st1 evs>>) /\ (<<HD: e = Some (event_sys ev)>>)))
  :
    _state_behaves' state_behaves' fuel st0 (Beh.cons ev evs)
.

Definition state_behaves': _ -> _ -> _ -> Prop := paco3 _state_behaves' bot3.

Lemma state_behaves'_mon: monotone3 _state_behaves'.
Proof.
  ii. inv IN.
  - econs 1; et.
  - econs 2; et.
  - econs 3; et.
  - econs 4; et.
  - econs 5; et. ii. exploit STEP; et. i; des. clarify. esplits; et.
  - rr in STEP. des. econs 6; et. rr. esplits; et.
  - econs 7; et. ii. exploit STEP; et. i; des. clarify. esplits; et.
  - rr in STEP. des. econs 8; et. rr. esplits; et.
Qed.

Hint Constructors _state_behaves'.
Hint Unfold state_behaves'.
Hint Resolve state_behaves'_mon: paco.

(* Inductive max_silent (st0: L.(state)): nat -> Prop := *)
(* | max_silent_base *)
(*     e st1 *)
(*     (SOME: L.(step) st0 (Some e) st1) *)
(*   : *)
(*     max_silent st0 0 *)
(* | max_silent_step *)
(*     st1 n *)
(*     (STEP: L.(step) st0 None st1) *)
(*     (TL: max_silent st1 n) *)
(*   : *)
(*     max_silent st0 (S n) *)
(* . *)

(* Require Import Lia. *)
(* Lemma max_silent_downward_closed *)
(*       n m st0 *)
(*       (MON: n <= m) *)
(*   : *)
(*     max_silent st0 m -> max_silent st0 n *)
(* . *)
(* Proof. *)
(*   i. ginduction H; ii; ss. *)
(*   - destruct n; ss; try lia; econs; et. *)
(*   - destruct n0; ss; try lia; econs; et. *)
(*     eapply IHmax_silent. lia. *)
(* Qed. *)

(* Theorem classical *)
(*         st0 *)
(*   : *)
(*     <<FIN: exists n, max_silent st0 n>> \/ <<INF: state_spin st0>> *)
(* . *)
(* Proof. *)
(*   destruct (classic (exists n, max_silent st0 n)); et. *)
(*   right. *)
(*   eapply diverge_spin. *)
(*   ii. *)
(*   eapply Classical_Pred_Type.not_ex_all_not with (n:=m) in H. Psimpl. *)
(*   des; et. *)

(* Qed. *)

(**********************
can we derive "max_silent" mechanically?
e.g. the index drops whenever an inductive call happens
***********************)
(**********************
TODO: CompCert랑 비교하고 이해: induction (star step)이 거기선 쉽고 왜 여기선 어려운가?
***********************)
Variable max_silent: L.(state) -> nat -> Prop.
Theorem equiv_aux
        st0 beh fuel
        (MAXSL: max_silent st0 fuel)
  :
    state_behaves st0 beh <-> state_behaves' fuel st0 beh
.
Proof.
  (*** TODO: well-founded induction ??? ***)
  split; intro B.
  - revert_until st0. revert st0. pcofix CIH. i. pfold. punfold B.
    destruct fuel.
    { admit. (*** max silent 0 ---> it should stuck or end here ***) }
    inv B; et.
    + econs 5; et. ii. exploit STEP; et. i; des. clarify. esplits; et. right. eapply CIH; et.
      admit. (*** max silent step ***)
    + econs 6; et. rr in STEP; des; clarify. rr; esplits; et. right. eapply CIH; et.
      admit. (*** max silent step ***)
    + econs 7; et. ii. exploit STEP; et. i; des. clarify. pclearbot.
      esplits; et. right. eapply CIH; et.
      { admit. (*** max silent step ?????????????????? ***) }
    + econs 8; et. rr in STEP; des; clarify. pclearbot.
      rr; esplits; et. right. eapply CIH; et.
      { admit. (*** max silent step ?????????????????? ***) }
  - revert_until st0. revert st0. pcofix CIH. i. pfold. punfold B.
    revert_until CIH. fix IH 5. i.
    inv B; try (by econs; et).
    + econs 5; et. ii. exploit STEP; et. i; des. clarify. esplits; et.
      eapply IH; et.
      { admit. (*** max silent step ***) }
      { pclearbot. }


    destruct fuel.
    { admit. (*** max silent 0 ---> it should stuck or end here ***) }
    inv B; et.
    + econs 5; et. ii. exploit STEP; et. i; des. clarify. esplits; et. right. eapply CIH; et.
      admit. (*** max silent step ***)
    + econs 6; et. rr in STEP; des; clarify. rr; esplits; et. right. eapply CIH; et.
      admit. (*** max silent step ***)
    + econs 7; et. ii. exploit STEP; et. i; des. clarify. pclearbot.
      esplits; et. right. eapply CIH; et.
      { admit. (*** max silent step ?????????????????? ***) }
    + econs 8; et. rr in STEP; des; clarify. pclearbot.
      rr; esplits; et. right. eapply CIH; et.
      { admit. (*** max silent step ?????????????????? ***) }
Qed.

Theorem equiv
        st0 beh
  :
    state_behaves st0 beh <-> exists fuel, state_behaves' fuel st0 beh
.
Proof.
  split; i.
  - admit.
  - des. revert_until L. pcofix CIH. i. pfold.
    punfold H0. inv H0; et.
    + econs 5; et. ii. exploit STEP; et. i; des. clarify. esplits; et. pclearbot.
Qed.





Definition program_behaves: Beh.t -> Prop := state_behaves L.(initial_state).

End BEHAVES.
Hint Constructors _state_spin.
Hint Unfold state_spin.
Hint Resolve state_spin_mon: paco.
Hint Constructors _state_behaves.
Hint Unfold state_behaves.
Hint Resolve state_behaves_mon: paco.

Lemma prefix_closed_ind
      L r st0 pre bh
      (BEH: _state_behaves L r st0 bh)
      (PRE: Beh.prefix pre bh)
      (COIND: forall st0 pre bh, r st0 bh -> Beh.prefix pre bh -> r st0 (Beh.app pre Beh.nb))
  :
    <<BEH: _state_behaves L r st0 (Beh.app pre Beh.nb)>>
.
Proof.
  revert_until r. fix IH 4. ii.
  rr in PRE. des. subst.
  inv BEH; destruct pre; ss.
  - econs 5; et. ii. exploit STEP; et. i; des. clarify. esplits; et.
    rewrite Beh.fold_app in *. eapply IH; et. rr. ss. esplits; et.
  - econs 6; et. rr in STEP. des. clarify. rr. esplits; eauto.
    rewrite Beh.fold_app in *. eapply IH; et. rr. ss. esplits; et.
  - econs 7; et. ii. exploit STEP; et. i; des. clarify. esplits; et.
    eapply COIND; et. rr. et.
  - econs 8; et. rr in STEP. des. clarify. rr. esplits; eauto.
    eapply COIND; et. rr. et.
Qed.

Lemma prefix_closed_coind
      L
      st0 pre bh
      (BEH: state_behaves L st0 bh)
      (PRE: Beh.prefix pre bh)
  :
    <<NB: state_behaves L st0 (Beh.app pre Beh.nb)>>
.
Proof.
  (* move IHpre at top. *)
  revert_until L. pcofix CIH. i. pfold.
  punfold BEH. rr in PRE. des.
  inv BEH; try (by destruct pre; ss).
  - econs 5; et. ii. exploit STEP; et. i; des. clarify. esplits; et.
    {
      (* clear STEP. *)
      revert_until CIH. fix IH 8. i.
      inv TL; destruct pre; ss.
      - econs 5; et. ii. exploit STEP1; et. i; des. clarify. esplits; et.
        rewrite Beh.fold_app in *. eapply IH; et.
      - econs 6; et. rr in STEP1. des. clarify. rr. esplits; eauto.
        rewrite Beh.fold_app in *. eapply IH; et. rr. ss. esplits; et.
      - econs 7; et. ii. exploit STEP; et. i; des. clarify. esplits; et.
        eapply COIND; et. rr. et.
      - econs 8; et. rr in STEP. des. clarify. rr. esplits; eauto.
        eapply COIND; et. rr. et.
    }
    
    eapply prefix_closed_ind with (pre:=pre) (bh:=(Beh.app pre tl)); et.
    { eapply state_behaves_mon; eauto. i. eapply upaco2_mon; eauto. ii; ss. }
    { rr. et. }
    { ii. right.
      TTTTTTTTTTTTTTTTTTTTTTT
    }
    assert(_state_behaves L (upaco2 (_state_behaves L) bot2) st1 (Beh.app pre Beh.nb)).
    {
      eapply prefix_closed_ind; et.
      { rr. et. }
      ii. pclearbot. right.
      clear - TL.
      remember (Beh.app pre tl) as tmp.
      ginduction TL; ii; ss; destruct pre; ss; clarify.
      - econs; et. ii. exploit STEP; et. i; des. clarify. esplits; et.
    }
    eapply state_behaves_mon; eauto. i. eapply upaco2_mon; eauto. ii; ss.
  - admit.
  - destruct pre; ss. clarify. econs 7; et. ii. exploit STEP; et. i; des. clarify. pclearbot.
    esplits; eauto. right. eapply CIH; et. rr; eauto.
  - destruct pre; ss. clarify. econs 8; et. rr in STEP. des. clarify. pclearbot.
    rr. esplits; et. right. eapply CIH; et. rr; eauto.
Qed.

Lemma prefix_closed
      L
      pre bh
      (BEH: program_behaves L bh)
      (PRE: Beh.prefix pre bh)
  :
    <<NB: program_behaves L (Beh.app pre Beh.nb)>>
.
Proof.
  (* ginduction pre; ss. *)
  (* { i. pfold. econs; et. } *)
  (* i. *)


  revert_until L. pcofix CIH. i. pfold.
  punfold BEH. rr in PRE. des.
  inv BEH; try (by destruct pre; ss).
  - econs 5; et. ii. exploit STEP; et. i; des. clarify.
    esplits; et.
  - destruct pre; ss.
  econs; et.
  pfold. econs; et.
Qed.

Lemma nb_bottom
      L
  :
    <<NB: program_behaves L Beh.nb>>
.
Proof. pfold. econs; et. Qed.
