From ITree Require Export ITree Subevent.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.
From ExtLib Require Export
     (* Data.String *)
     (* Structures.Monad *)
     (* Structures.Traversable *)
     (* Structures.Foldable *)
     (* Structures.Reducible *)
     (* OptionMonad *)
     Functor FunctorLaws
     Structures.Maps
     (* Data.List *)
.
Require Import Coqlib.

Export SumNotations.
(* Export ITreeNotations. *)
Export Monads.
(* Export MonadNotation. *)
(* Export FunctorNotation. *)
Export CatNotations.
Open Scope cat_scope.
Open Scope monad_scope.
Open Scope itree_scope.

Set Implicit Arguments.


Module ITreeNotations2.
Notation "t1 >>= k2" := (ITree.bind t1 k2)
  (at level 58, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 62, t1 at next level, right associativity) : itree_scope.
Notation "` x : t <- t1 ;; t2" := (ITree.bind t1 (fun x : t => t2))
  (at level 62, t at next level, t1 at next level, x ident, right associativity) : itree_scope.
Notation "t1 ;;; t2" := (ITree.bind t1 (fun _ => t2))
  (at level 62, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
  (at level 62, t1 at next level, p pattern, right associativity) : itree_scope.
Infix ">=>" := ITree.cat (at level 62, right associativity) : itree_scope.
Notation "f <$> x" := (@fmap _ _ _ _ f x) (at level 61, left associativity).
End ITreeNotations2.

Export ITreeNotations2.



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

Lemma map_vis {E R1 R2 X} (e: E X) (k: X -> itree E R1) (f: R1 -> R2) :
  (* (f <$> (Vis e k)) ≅ Vis e (fun x => f <$> (k x)). *)
  ITree.map f (Vis e k) = Vis e (fun x => f <$> (k x)).
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

Lemma bind_ret_r_rev : forall (E : Type -> Type) (R : Type) (s : itree E R), s = ` x : R <- s;; Ret x.
Proof.
  i. symmetry. apply bind_ret_r.
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

Lemma unfold_bind:
forall {E : Type -> Type} {R S : Type} (t : itree E R) (k : R -> itree E S),
` x : _ <- t;; k x
= match observe t with
  | RetF r => k r
  | TauF t0 => tau;; ` x : _ <- t0;; k x
  | @VisF _ _ _ X e ke => Vis e (fun x : X => ` x : _ <- ke x;; k x)
  end.
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

Lemma interp_state_bind:
  forall (E F : Type -> Type) (A B S : Type) (f : forall T : Type, E T -> S -> itree F (S * T)) (t : itree E A)
         (k : A -> itree E B) (s : S),
    interp_state f (` x : _ <- t;; k x) s = ` st : S * A <- interp_state f t s;; interp_state f (k (snd st)) (fst st)
.
Proof. i. f. apply interp_state_bind. Qed.

Lemma interp_state_vis:
  forall (E F : Type -> Type) (S T U : Type) (e : E T) (k : T -> itree E U) (h : forall T0 : Type, E T0 -> stateT S (itree F) T0)
         (s : S), interp_state h (Vis e k) s = ` sx : S * T <- h T e s;; (tau;; interp_state h (k (snd sx)) (fst sx))
.
Proof.
  i. f. apply interp_state_vis.
Qed.

Lemma interp_state_tau :
  forall (E F : Type -> Type) (S T : Type) (t : itree E T) (h : forall T0 : Type, E T0 -> stateT S (itree F) T0) (s : S),
    interp_state h (tau;; t) s = (tau;; interp_state h t s)
.
Proof.
  i. f. apply interp_state_tau.
Qed.

Lemma interp_state_ret:
  forall (E F : Type -> Type) (R S : Type) (f : forall T : Type, E T -> S -> itree F (S * T)) (s : S) (r : R),
    interp_state f (Ret r) s = Ret (s, r)
.
Proof.
  i. f. apply interp_state_ret.
Qed.

Lemma unfold_interp:
  forall (E F : Type -> Type) (R : Type) (f : forall T : Type, E T -> itree F T) (t : itree E R),
    interp f t = _interp f (observe t)
.
Proof.
  i. f. apply unfold_interp.
Qed.
Lemma interp_ret:
  forall (E F : Type -> Type) (R : Type) (f : forall T : Type, E T -> itree F T) (x : R), interp f (Ret x) = Ret x.
Proof. i. f. apply interp_ret. Qed.

Lemma interp_tau:
  forall {E F : Type -> Type} {R : Type} {f : forall T : Type, E T -> itree F T} (t : itree E R),
    interp f (tau;; t) = (tau;; interp f t)
.
Proof. i. f. apply interp_tau. Qed.

(*** Original name: interp_state_trigger_eqit ***)
Lemma interp_state_trigger:
  forall (E F : Type -> Type) (R S : Type) (e : E R) (f : forall T : Type, E T -> stateT S (itree F) T) (s : S),
    interp_state f (ITree.trigger e) s = ` x : S * R <- f R e s;; (tau;; Ret x)
.
Proof. i. f. apply interp_state_trigger_eqit. Qed.

(*** TODO: interp_trigger_eqit does not exist. report to itree people? ***)
Lemma interp_trigger:
  forall (E F : Type -> Type) (R : Type) (e : E R) (f : E ~> itree F),
    interp f (ITree.trigger e) = x <- f R e;; tau;; Ret x
.
Proof. i. f. rewrite unfold_interp. ss. f_equiv; ii. rewrite interp_ret. refl. Qed.

Lemma interp_bind :
forall {E F : Type -> Type} {R S : Type} (f : forall T : Type, E T -> itree F T)
  (t : itree E R) (k : R -> itree E S),
interp f (` x : _ <- t;; k x) = ` r : R <- interp f t;; interp f (k r).
Proof. i. f. apply interp_bind. Qed.

Lemma interp_mrec_hit:
  forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (a : D U),
    interp_mrec ctx (trigger a) = (tau;; interp_mrec ctx (ctx _ a))
.
Proof.
  i. rewrite unfold_interp_mrec. ss.
  unfold resum, ReSum_id, id_, Id_IFun. rewrite bind_ret_r. ss.
Qed.

(*** TODO: I don't want "F" here, but it is technically needed. Report it to itree people? ***)
Lemma interp_mrec_miss:
  (* forall (D E F: Type -> Type) `{F -< E} (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (a : F U), *)
  forall (D E F: Type -> Type) `{F -< E} (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (a : F U),
    interp_mrec ctx (trigger a) = x <- (trigger a);; tau;; Ret x
(* (trigger a) >>= tauK *)
.
Proof.
  i. rewrite unfold_interp_mrec. cbn.
  unfold trigger. irw.
  f; repeat (f_equiv; ii; des_ifs_safe); f.
  irw. ss.
Qed.

Lemma interp_mrec_tau
      D E
      (ctx : forall T : Type, D T -> itree (D +' E) T)
      U
      (itr: itree (D +' E) U)
  :
    interp_mrec ctx (tau;; itr) = (tau;; interp_mrec ctx itr)
.
Proof. rewrite unfold_interp_mrec at 1. cbn. refl. Qed.

Lemma interp_mrec_ret
      D E
      (ctx : forall T : Type, D T -> itree (D +' E) T)
      U
      (u: U)
  :
    interp_mrec ctx (Ret u) = Ret u
.
Proof. rewrite unfold_interp_mrec at 1. cbn. refl. Qed.

Lemma interp_interp:
  forall {E F G : Type -> Type} {R : Type} (f : forall T : Type, E T -> itree F T) (g : forall T : Type, F T -> itree G T) (t : itree E R),
    interp g (interp f t) = interp (fun (T : Type) (e : (fun H : Type => E H) T) => interp g (f T e)) t.
Proof. i. f. apply interp_interp. Qed.

Lemma subst_bind: forall E T U (k: T -> itree E U) i, ITree.subst k i = ITree.bind i k.
Proof. i. refl. Qed.

Ltac iby3 TAC :=
  first [
      instantiate (1:= fun _ _ _ => _); TAC|
      instantiate (1:= fun _ _ _ => _ <- _ ;; _); TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- _ ;; _) ;; _); TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- _ ;; _) ;; _) ;; _); TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _); TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _) ;; _); TAC|
      fail
    ]
.

Ltac iby1 TAC :=
  first [
      instantiate (1:= fun '(_, (_, _)) => _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- _ ;; _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- _ ;; _) ;; _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- (_ <- _ ;; _) ;; _) ;; _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _) ;; _); TAC|
      fail
    ]
.

(* Ltac grind :=  f; repeat (f_equiv; ii; des_ifs_safe); f. *)

Ltac ired := repeat (try rewrite subst_bind;
                     try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau;
                     (* try rewrite interp_vis; *)
                     try rewrite interp_ret;
                     try rewrite interp_tau;
                     (* try rewrite interp_trigger *)
                     try rewrite interp_bind;

                     try rewrite interp_mrec_hit;
                     try rewrite interp_mrec_miss;
                     try rewrite interp_mrec_bind;
                     try rewrite interp_mrec_tau;
                     try rewrite interp_mrec_ret;

                     try rewrite interp_state_trigger;
                     try rewrite interp_state_bind;
                     try rewrite interp_state_tau;
                     try rewrite interp_state_ret;
                     cbn
                    ).
(* first [eapply eqit_VisF|f_equiv] *)
(* Ltac grind := repeat (ired; f; repeat (f_equiv; match goal with [ |- context[going] ] => fail | _ => idtac end; ii; des_ifs_safe); f). *)
(* Ltac grind := repeat (ired; f; repeat (Morphisms.f_equiv; ii; des_ifs_safe); f). *)
Ltac grind := repeat (ired; match goal with
                            (* | [ |- tau;; ?a = tau;; ?b ] => do 2 f_equal *)
                            | [ |- (go (TauF ?a)) = (go (TauF ?b)) ] => do 2 f_equal
                            | [ |- (_ <- _ ;; _) = (_ <- _ ;; _) ] => Morphisms.f_equiv; apply func_ext_dep; i
                            | _ => idtac
                            end; ii; des_ifs_safe).
(*** simple regression tests ***)
Goal forall E R (itr: itree E R), (tau;; tau;; tau;; itr) = (tau;; tau;; itr). i. grind. Abort.
Goal forall E X Y (itr: itree E X) (ktr: X -> itree E Y), ((x <- itr;; tau;; tau;; Ret x) >>= ktr) = ((x <- itr;; tau;; Ret x) >>= ktr).
  i. progress grind. (*** it should progress ***)
Abort.







Definition update K V map `{Map K V map}: K -> (V -> V) -> map -> option map :=
  fun k f m => do v <- Maps.lookup k m ; Some (Maps.add k (f v) m)
.

Lemma unfold_update
      K V map `{Map K V map}
      k vf m
  :
    update k vf m = match lookup k m with
                    | Some v => Some (add k (vf v) m)
                    | None => None
                    end
.
Proof. unfold update. uo. des_ifs. Qed.

Hint Unfold update.



Inductive taus E R: itree E R -> nat -> Prop :=
| taus_tau
    itr0 n
    (TL: taus itr0 n)
  :
    taus (Tau itr0) (1 + n)
| taus_ret
    r
  :
    taus (Ret r) 0
| taus_vis
    X (e: E X) k
  :
    taus (Vis e k) 0
.

Lemma unfold_spin
      E R
  :
    (@ITree.spin E R) = tau;; ITree.spin
.
Proof.
  rewrite itree_eta_ at 1. cbn. refl.
Qed.

Lemma spin_no_ret
      E R
      r
      (SIM: @ITree.spin E R ≈ Ret r)
  :
    False
.
Proof.
  punfold SIM.
  r in SIM. cbn in *.
  dependent induction SIM; ii; clarify.
  - eapply IHSIM; ss.
Qed.

Lemma spin_no_vis
      E R
      X (e: E X) k
      (SIM: @ITree.spin E R ≈ Vis e k)
  :
    False
.
Proof.
  punfold SIM.
  r in SIM. cbn in *.
  dependent induction SIM; ii; clarify.
  - eapply IHSIM; ss.
Qed.





Theorem diverge_spin
        E R
        (itr: itree E R)
        (DIVERGE: forall m, ~taus itr m)
  :
    <<SPIN: itr = ITree.spin>>
.
Proof.
  r. f.
  revert_until R.
  ginit.
  gcofix CIH. i. gstep.
  rewrite unfold_spin.
  ides itr; swap 2 3.
  { contradict DIVERGE. ii. eapply H. econs; et. }
  { contradict DIVERGE. ii. eapply H. econs; et. }
  econs; eauto.
  gbase. eapply CIH. ii. eapply DIVERGE. econs; eauto.
Qed.

Theorem spin_diverge
        E R
        (itr: itree E R)
        (SPIN: itr = ITree.spin)
  :
    <<DIVERGE: forall m, ~taus itr m>>
.
Proof.
  ii. clarify.
  ginduction m; ii; ss.
  { inv H.
    - rewrite unfold_spin in *. ss.
    - rewrite unfold_spin in *. ss.
  }
  inv H.
  rewrite unfold_spin in *. ss. clarify. eauto.
Qed.

Theorem case_analysis
        E R
        (itr: itree E R)
  :
    (<<CONVERGE: exists (m: nat), taus itr m>>)
    \/ (<<DIVERGE: itr = ITree.spin>>)
.
Proof.
  destruct (classic (exists m, taus itr m)); et.
  right.
  eapply diverge_spin.
  ii.
  eapply Classical_Pred_Type.not_ex_all_not with (n:=m) in H. Psimpl.
  des; et.
Qed.

Theorem spin_spin
        E R
        (i_src i_tgt: itree E R)
        (SPIN: i_src = ITree.spin)
        (SIM: i_src ≈ i_tgt)
  :
    <<SPIN: i_tgt = ITree.spin>>
.
Proof.
  clarify.
  r. f.
  revert_until R.
  ginit.
  gcofix CIH. i. gstep.
  rewrite unfold_spin.
  ides i_tgt; swap 2 3.
  { apply spin_no_ret in SIM. ss. }
  { apply spin_no_vis in SIM. ss. }
  econs; eauto.
  gbase. eapply CIH. rewrite tau_eutt in SIM. ss.
Qed.

Definition resum_itr E F `{E -< F}: itree E ~> itree F := fun _ itr => interp (fun _ e => trigger e) itr.

Definition tauK {E R}: R -> itree E R := fun r => tau;; Ret r.
Hint Unfold tauK.

Definition idK {E R}: R -> itree E R := fun r => Ret r.
Hint Unfold idK.

Lemma idK_spec E R (i0: itree E R): i0 = i0 >>= idK. Proof. unfold idK. irw. refl. Qed.






(* (* Notation Checking *) *)
(* From iris.bi Require Import derived_connectives updates internal_eq plainly. *)
(* From iris.base_logic Require Import upred. *)
(* From iris.prelude Require Import options. *)

Ltac resub :=
  repeat multimatch goal with
         | |- context[@ITree.trigger ?E ?R ?e] =>
           match e with
           | subevent _ _ => idtac
           | _ => replace (@ITree.trigger E R e) with (trigger e) by refl
           end
         | |- context[@subevent _ ?F ?prf _ (?e|)%sum] =>
           let my_tac := ltac:(fun H => replace (@subevent _ F prf _ (e|)%sum) with (@subevent _ F _ _ e) by H) in
           match (type of e) with
           | (_ +' _) _ => my_tac ltac:(destruct e; refl)
           | _ => my_tac ltac:(refl)
           end
         | |- context[@subevent _ ?F ?prf _ (|?e)%sum] =>
           let my_tac := ltac:(fun H => replace (@subevent _ F prf _ (|e)%sum) with (@subevent _ F _ _ e) by H) in
           match (type of e) with
           | (_ +' _) _ => my_tac ltac:(destruct e; refl)
           | _ => my_tac ltac:(refl)
           end
         | |- context[ITree.trigger (@subevent _ ?F ?prf _ (resum ?a ?b ?e))] =>
           replace (ITree.trigger (@subevent _ F prf _ (resum a b e))) with (ITree.trigger (@subevent _ F _ _ e)) by refl
         end.

Definition resum_ktr A E F `{E -< F}: ktree E A ~> ktree F A := fun _ ktr a => resum_itr (ktr a).
Definition trivial_Handler `{E -< F}: Handler E F := fun T X => trigger X.

Lemma observe_eta E R (itr0 itr1: itree E R)
      (EQ: _observe itr0 = _observe itr1)
  :
    itr0 = itr1.
Proof.
  erewrite (itree_eta_ itr0).
  erewrite (itree_eta_ itr1).
  f_equal. auto.
Qed.
