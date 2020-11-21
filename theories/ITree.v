From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

From ITree Require Import
     ITree ITreeFacts EqAxiom.

From Paco Require Import paco.

Require Import Universe.
Require Import sflib STS Behavior.
Require Import Program.

Import ITreeNotations.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.



Set Implicit Arguments.

Axiom prop_ext: ClassicalFacts.prop_extensionality.
Tactic Notation "sym" "in" hyp(H) := symmetry in H.
Ltac refl := reflexivity.
Ltac sym := symmetry.














Lemma eq_is_bisim: forall E R (t1 t2 : itree E R), t1 = t2 -> t1 ≅ t2.
Proof. ii. clarify. reflexivity. Qed.
Lemma bisim_is_eq: forall E R (t1 t2 : itree E R), t1 ≅ t2 -> t1 = t2.
Proof. ii. eapply bisimulation_is_eq; eauto. Qed.



Ltac f := first [eapply bisim_is_eq|eapply eq_is_bisim].
Tactic Notation "f" "in" hyp(H) := first [eapply bisim_is_eq in H|eapply eq_is_bisim in H].
Ltac ides itr :=
  let T := fresh "T" in
  destruct (observe itr) eqn:T;
  sym in T; apply simpobs in T; apply bisim_is_eq in T; rewrite T in *; clarify.
Ltac csc := clarify; simpl_depind; clarify.

Notation "tau;; t2" := (Tau t2)
  (at level 200, right associativity) : itree_scope.



(*** COPIED FROM MASTER BRANCH. REMOVE LATER ***)
(*** COPIED FROM MASTER BRANCH. REMOVE LATER ***)
(*** COPIED FROM MASTER BRANCH. REMOVE LATER ***)
Lemma eutt_eq_bind : forall E R U (t1 t2: itree E U) (k1 k2: U -> itree E R), t1 ≈ t2 -> (forall u, k1 u ≈ k2 u) -> ITree.bind t1 k1 ≈ ITree.bind t2 k2.
Proof.
  intros.
  eapply eutt_clo_bind with (UU := Logic.eq); [eauto |].
  intros ? ? ->. apply H0.
Qed.
Ltac f_equiv := first [eapply eutt_eq_bind|eapply eqit_VisF|Morphisms.f_equiv].
(* eapply eqit_bind'| *)

Hint Rewrite @bind_trigger : itree.
Hint Rewrite @tau_eutt : itree.
Hint Rewrite @bind_tau : itree.

(* Tactic Notation "irw" "in" ident(H) := repeat (autorewrite with itree in H; cbn in H). *)
(* Tactic Notation "irw" := repeat (autorewrite with itree; cbn). *)

(*** TODO: IDK why but (1) ?UNUSNED is needed (2) "fold" tactic does not work. WHY????? ***)
Ltac fold_eutt :=
  repeat multimatch goal with
         | [ H: eqit eq true true ?A ?B |- ?UNUSED ] =>
           let name := fresh "tmp" in
           assert(tmp: eutt eq A B) by apply H; clear H; rename tmp into H
         end
.

Lemma bind_ret_map {E R1 R2} (u : itree E R1) (f : R1 -> R2) :
  (r <- u ;; Ret (f r)) = Functor.fmap f u.
Proof.
  f.
  rewrite <- (bind_ret_r u) at 2. apply eqit_bind.
  - hnf. intros. apply eqit_Ret. auto.
  - rewrite bind_ret_r. reflexivity.
Qed.

Lemma map_vis {E R1 R2 X} (e: E X) (k: X -> itree E R1) (f: R1 -> R2) :
  (* (f <$> (Vis e k)) ≅ Vis e (fun x => f <$> (k x)). *)
  ITree.map f (Vis e k) = Vis e (fun x => Functor.fmap f (k x)).
Proof.
  f.
  cbn.
  unfold ITree.map.
  autorewrite with itree. refl.
Qed.




(*** TODO: move to SIRCommon ***)
Lemma unfold_interp_mrec :
forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) 
  (R : Type) (t : itree (D +' E) R), interp_mrec ctx t = _interp_mrec ctx (observe t).
Proof.
  i. f. eapply unfold_interp_mrec; et.
Qed.

Lemma bind_ret_l : forall (E : Type -> Type) (R S : Type) (r : R) (k : R -> itree E S),
    ` x : _ <- Ret r;; k x = k r.
Proof.
  i. f. eapply bind_ret_l.
Qed.

Lemma bind_ret_r : forall (E : Type -> Type) (R : Type) (s : itree E R), ` x : R <- s;; Ret x = s.
Proof.
  i. f. eapply bind_ret_r.
Qed.

Lemma bind_tau : forall (E : Type -> Type) (R U : Type) (t : itree E U) (k : U -> itree E R),
  ` x : _ <- Tau t;; k x = Tau (` x : _ <- t;; k x).
Proof.
  i. f. eapply bind_tau.
Qed.

Lemma bind_vis: forall (E : Type -> Type) (R U V : Type) (e : E V) (ek : V -> itree E U) (k : U -> itree E R),
  ` x : _ <- Vis e ek;; k x = Vis e (fun x : V => ` x : _ <- ek x;; k x).
Proof.
  i. f. eapply bind_vis.
Qed.

Lemma bind_trigger: forall (E : Type -> Type) (R U : Type) (e : E U) (k : U -> itree E R),
    ` x : _ <- ITree.trigger e;; k x = Vis e (fun x : U => k x).
Proof. i. f. eapply bind_trigger. Qed.

Lemma bind_bind : forall (E : Type -> Type) (R S T : Type) (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ` x : _ <- (` x : _ <- s;; k x);; h x = ` r : R <- s;; ` x : _ <- k r;; h x.
Proof. i. f. eapply bind_bind. Qed.

Lemma unfold_bind :
forall (E : Type -> Type) (R S : Type) (t : itree E R) (k : R -> itree E S),
` x : _ <- t;; k x = ITree._bind k (fun t0 : itree E R => ` x : _ <- t0;; k x) (observe t).
Proof. i. f. apply unfold_bind. Qed.

Lemma interp_mrec_bind:
  forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T)
         (U T : Type) (t : itree (D +' E) U) (k : U -> itree (D +' E) T),
    interp_mrec ctx (` x : _ <- t;; k x) = ` x : U <- interp_mrec ctx t;; interp_mrec ctx (k x)
.
Proof. ii. f. eapply interp_mrec_bind. Qed.


Hint Rewrite unfold_interp_mrec : itree_axiom.
Hint Rewrite bind_ret_l : itree_axiom.
Hint Rewrite bind_ret_r : itree_axiom.
Hint Rewrite bind_tau : itree_axiom.
Hint Rewrite bind_vis : itree_axiom.
Hint Rewrite bind_trigger : itree_axiom.
Hint Rewrite bind_bind : itree_axiom.
Tactic Notation "irw" "in" ident(H) := repeat (autorewrite with itree_axiom in H; cbn in H).
Tactic Notation "irw" := repeat (autorewrite with itree_axiom; cbn).












Inductive eventE: Type -> Type :=
| syscall (ev: event): eventE unit
| choose X: eventE X
| take X: eventE X
.

Definition sir := itree eventE val.



Section TRANS.
  Variable sem: semantics.

  Inductive stepE: Type -> Type :=
  (* | demonic_go: stepE unit *)
  (* | angelic_go: stepE unit *)
  (* | get_sort: stepE sort *)
  | go: stepE (option val)
  .

  Definition match_trans _trans: itree (stepE +' eventE) val := 
    rv <- trigger go;;
     match rv with
     | Some rv => Ret rv
     | _ => Tau _trans
     end
  .

  CoFixpoint _trans: itree (stepE +' eventE) val := match_trans _trans.

  Theorem unfold_trans: _trans = match_trans _trans.
  Proof.
    destruct (observe _trans) eqn:T; sym in T; apply simpobs in T; f in T; rewrite T.
    { f in T. punfold T. inv T. }
    { f in T. punfold T. inv T. inv REL; csc. }
    destruct e; ss; cycle 1.
    { f in T. punfold T. inv T. csc. }
    destruct s; ss.
    (*** We don't have enough information here... ***)
    (*** morally, we should be able to prove below, but it is hard... ***)
    (* assert(k = fun rv => match rv with | Some rv => Ret rv | _ => Tau _trans end). *)
    rename T into U.
    destruct (observe (match_trans (Vis (inl1 go) k))) eqn:T;
      sym in T; apply simpobs in T; f in T; rewrite T.
    { f in T. punfold T. inv T. }
    { f in T. punfold T. inv T. inv REL; csc. }
    unfold match_trans in T. irw in T. csc.
  Abort.
  (*** TODO: Why is this proof hard??? ***)

  Theorem unfold_trans: _trans = match_trans _trans.
    assert(observing eq _trans (match_trans _trans)).
    {
      constructor. reflexivity.
    }
    f. rewrite <- H. f. ss.
  Qed.

  (* CoFixpoint _trans: itree (stepE +' eventE) val := *)
  (*   rv <- trigger go;; *)
  (*    match rv with *)
  (*    | Some rv => Ret rv *)
  (*    | _ => Tau _trans *)
  (*    end *)
  (* . *)

  (* Definition match_trans: itree (stepE +' eventE) val :=  *)
  (*   rv <- trigger go;; *)
  (*    match rv with *)
  (*    | Some rv => Ret rv *)
  (*    | _ => Tau _trans *)
  (*    end *)
  (* . *)

  (* Theorem unfold_trans: _trans = match_trans. *)
  (* Proof. *)
  (*   { *)
  (*     f. cofix CIH. *)
  (*     unfold _trans. unfold match_trans. *)
  (*     Guarded. *)
  (*   } *)
  (*   { *)
  (*     f. *)
  (*     pcofix CIH. *)
  (*     destruct (observe _trans) eqn:T; sym in T; apply simpobs in T; f in T; rewrite T. *)
  (*     - f in T. punfold T. inv T. *)
  (*     - f in T. punfold T. inv T. inv REL; csc. *)
  (*     - destruct e; ss; cycle 1. *)
  (*       { f in T. punfold T. inv T; csc. } *)
  (*       destruct s; ss. *)
  (*       assert(k = fun rv => match rv with | Some rv => Ret rv | _ => Tau _trans end). *)
  (*       { apply FunctionalExtensionality.functional_extensionality. i. *)
  (*         rename T into U. *)
  (*         destruct (observe _trans) eqn:T; sym in T; apply simpobs in T; f in T; rewrite T in *; ss. *)
  (*         f. clear - T. revert_until k. revert k. pcofix CIH. i. *)
  (*         des_ifs. *)
  (*         - destruct (observe _trans) eqn:U; sym in U; apply simpobs in U; f in U. *)
  (*           + rewrite U. *)
  (*           ss. *)
  (*         des_ifs. apply func_ext. admit "". } *)
  (*       unfold match_trans. *)
  (*       pfold. unfold trigger. irw. econs; eauto. ii. r. irw. des_ifs. *)
  (*       + subst. left. pfold. econs; eauto. *)
  (*       + left. pfold; econs; eauto. left. *)
  (*         eapply paco2_mon. *)
  (*         { f. ss. } *)
  (*         ii; ss. *)
  (*   } *)
  (* Qed. *)

  Definition h_stepE {E} `{eventE -< E}: stepE ~> stateT sem.(STS.state) (itree E) :=
    fun _ 'go st0 =>
      match sem.(state_sort) st0 with
      | demonic =>
        _st1 <- trigger (choose {st1 & sem.(STS.step) st0 None st1});;
        let st1 := projT1 _st1 in
        Ret (st1, None)
      | angelic =>
        _st1 <- trigger (take {st1 & sem.(STS.step) st0 None st1});;
        let st1 := projT1 _st1 in
        Ret (st1, None)
      | final rv =>
        Ret (st0, Some rv)
      | STS.vis =>
        (*** choose, take, exists, forall, all shouldn't matter, morally ***)
        _ev_st1 <- trigger (choose {ev_st1 & sem.(STS.step) st0 (Some (fst ev_st1)) (snd ev_st1)});;
        let '(ev, st1) := projT1 _ev_st1 in
        trigger (syscall ev);;
        Ret (st1, None)
      end
  .

  Definition i_stepE {E} `{eventE -< E} {A} (t : itree (stepE +' E) A) :
    stateT sem.(STS.state) (itree E) A :=
    let t' := State.interp_state (case_ h_stepE State.pure_state) t in
    t'
  .

  Definition trans: itree eventE val := '(_, rv) <- (i_stepE _trans sem.(initial_state));; Ret rv.

End TRANS.



Section INTERP.
  Variable itr: sir.

  Inductive istep: sir -> option event -> sir -> Prop :=
  | istep_tau
      itr
    :
      istep (Tau itr) None itr
  | istep_syscall
      k ev
      st1
      (ST1: st1 = k tt)
    :
      istep (Vis (subevent _ (syscall ev)) k) (Some ev) st1
  | istep_demonic
      X (x: X) k
      st1
      (ST1: st1 = k x)
    :
      istep (Vis (subevent _ (choose X)) k) None st1
  | istep_angelic
      X (x: X) k
      st1
      (ST1: st1 = k x)
    :
      istep (Vis (subevent _ (take X)) k) None st1
  .

  Definition istate_sort (st0: sir): sort :=
    match observe st0 with
    | TauF _ => demonic
    | RetF rv => final rv
    | VisF (syscall ev) k => STS.vis
    | VisF (choose X) k => demonic
    | VisF (take X) k => angelic
    end
  .

  Program Definition interp: semantics := {|
    STS.state := itree eventE val;
    step := istep;
    initial_state := itr;
    state_sort := istate_sort;
  |}
  .
  Next Obligation.
    inv STEP; inv STEP0; ss.
    simpl_existT. clarify.
  Qed.
  Next Obligation.
    inv STEP; ss.
  Qed.
  Next Obligation.
    inv STEP; ss.
  Qed.

End INTERP.







Lemma interp_state_ret:
  forall (E F : Type -> Type) (R S : Type) (f : forall T : Type, E T -> S -> itree F (S * T)) 
    (s : S) (r : R), State.interp_state f (Ret r) s = Ret (s, r).
Proof. i. f. eapply interp_state_ret. Qed.

Lemma unfold_interp_state:
  forall (E F : Type -> Type) (S R : Type) (h : forall T : Type, E T -> stateT S (itree F) T)
    (t : itree E R) (s : S), State.interp_state h t s = _interp_state h (observe t) s.
Proof. i. f. eapply unfold_interp_state. Qed.

Lemma interp_state_bind:
  forall (E F : Type -> Type) (A B S : Type) (f : forall T : Type, E T -> S -> itree F (S * T))
    (t : itree E A) (k : A -> itree E B) (s : S),
  State.interp_state f (` x : _ <- t;; k x) s
  = ` st : S * A <- State.interp_state f t s;; State.interp_state f (k (snd st)) (fst st).
Proof. i. f. eapply interp_state_bind. Qed.

Lemma interp_state_vis:
  forall (E F : Type -> Type) (S T U : Type) (e : E T) (k : T -> itree E U)
    (h : forall T0 : Type, E T0 -> stateT S (itree F) T0) (s : S),
  State.interp_state h (Vis e k) s
  = ` sx : S * T <- h T e s;; (tau;; State.interp_state h (k (snd sx)) (fst sx)).
Proof. i. f. eapply interp_state_vis. Qed.

Lemma interp_state_tau:
  forall (E F : Type -> Type) (S T : Type) (t : itree E T)
    (h : forall T0 : Type, E T0 -> stateT S (itree F) T0) (s : S),
  State.interp_state h (tau;; t) s = (tau;; State.interp_state h t s).
Proof. i. f. eapply interp_state_tau. Qed.












Ltac srw :=
  repeat (try rewrite interp_state_vis; try rewrite interp_state_bind;
          try rewrite interp_state_tau;
          try rewrite unfold_interp_state
         ).
Tactic Notation "srw" "in" hyp(H) :=
  repeat (try rewrite interp_state_vis in H; try rewrite interp_state_bind in H;
          try rewrite interp_state_tau in H;
          try rewrite unfold_interp_state in H
         ).

Theorem adq
        sem
  :
    Beh.of_program (interp (trans sem)) = (Beh.of_program sem)
.
Proof.
  apply FunctionalExtensionality.functional_extensionality. intro tr.
  apply prop_ext. split; intro A; cycle 1.
  { r in A. ss. r. ss.
    unfold trans at 2.
    abstr (initial_state sem) st0.
    revert_until sem. pcofix CIH. i.
    punfold A. inv A.
    - ss. unfold i_stepE.
      rewrite unfold_trans; unfold match_trans. irw. pfold.
      srw.
      irw. des_ifs. irw.
      econs 6; ss.
      rr. esplits; eauto.
      { ss. econs; eauto. }
      econs 1; ss.
    - admit "spin-spin".
    - admit "STUCK: this case is spurious; we can remove it in the definition".
    - pfold. econs; et.
    - pclearbot. ss. pfold.
      (* econs 5; eauto. *)
      (* { ss. unfold istate_sort. *)
      (*   rewrite unfold_trans. unfold match_trans. irw. *)
      (*   des_ifs; sym in Heq; apply simpobs in Heq. *)
      (*   - unfold i_stepE in Heq. f in Heq. srw in Heq. irw in Heq. des_ifs; irw in Heq; ss. *)
      (*   - unfold i_stepE in Heq. f in Heq. srw in Heq. irw in Heq. des_ifs; irw in Heq; ss. *)
      (*   - unfold i_stepE in Heq. f in Heq. srw in Heq. irw in Heq. des_ifs; irw in Heq; ss. *)
      (* } *)
      econs 6; eauto.
      { ss. clear - CIH SRT. unfold istate_sort.
        rewrite unfold_trans. unfold match_trans. irw.
        des_ifs; sym in Heq; apply simpobs in Heq.
        - unfold i_stepE in Heq. f in Heq. srw in Heq. irw in Heq. des_ifs; irw in Heq; ss.
        - unfold i_stepE in Heq. f in Heq. srw in Heq. irw in Heq. des_ifs; irw in Heq; ss.
        - unfold i_stepE in Heq. f in Heq. srw in Heq. irw in Heq. des_ifs; irw in Heq; ss.
      }
      rr. esplits; eauto.
      { ss. unfold i_stepE. rewrite unfold_trans; unfold match_trans. srw. irw. des_ifs.
        irw. econs 3; eauto.
      }
      Unshelve. all: cycle 1.
      { exists (ev, st2). ss. }
      ss. econs 5; ss.
      { irw. econs 2; eauto. }
      right.
      assert(BDOOR: forall E R (itr: itree E R), (tau;; itr) = itr).
      { admit "TODO: need stronger coind hyp.". }
      rewrite BDOOR.
      srw. irw. srw. rewrite BDOOR. rewrite <- unfold_interp_state. eapply CIH; et.
    - admit "TODO: demonic".
    - admit "TODO: angelic".
  }
  { r in A. ss. r. ss.
    unfold trans in A at 2.
    abstr (initial_state sem) st0.
    revert_until sem. pcofix CIH. i.
    punfold A. inv A.
    - ss. unfold istate_sort in *. des_ifs. sym in Heq. apply simpobs in Heq. f in Heq.
      unfold i_stepE in Heq.
      rewrite unfold_interp_state in Heq. ss.
      destruct (observe _trans) eqn:T; ss. destruct e; ss. destruct s; ss.
      cbn in *. des_ifs; csc; irw in Heq; csc.
    - admit "TODO: spin-spin".
    - admit "STUCK: this case is spurious; we can remove it in the definition".
    - pfold. econs; eauto.
    - ss. unfold istate_sort in *. des_ifs. sym in Heq. apply simpobs in Heq. f in Heq.
      clear_tac. pclearbot.
      inv STEP. rewrite Heq in *. csc.
      punfold TL; cycle 1.
      { (*** TODO: Why didn't hint work? univ problem? ***)
        eapply (@Beh.of_state_mon (interp (trans sem))). }
      rewrite unfold_trans in Heq. unfold match_trans in Heq. irw in Heq.
      unfold i_stepE in Heq. srw in Heq. irw in Heq. des_ifs; irw in Heq; simpl_depind.
    - admit "TODO: demonic".
    - admit "TODO: angelic".
  }
Qed.
