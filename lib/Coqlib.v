Require Export ZArith.
Require Export Znumtheory.
Require Export List.
Require Export Bool.

Ltac check_safe := let n := numgoals in guard n < 2.
Require Export sflib.
From Paco Require Export paco.
Notation "f ∘ g" := (fun x => (f (g x))). (*** TODO: move to Coqlib ***)
Require Export Basics.

Require Import Relations.
Require Export RelationClasses.
Require Import Wellfounded.
Require Export Classical_Prop.
Require Export Lia.
Require Export Axioms.
Require Import Relation_Operators.
Require Export List.
Require Export ClassicalDescription.
Require Export Program.
Require Export Morphisms.
Require Import Sorting.Permutation.

Set Implicit Arguments.



Global Generalizable All Variables.
(* Global Unset Transparent Obligations. *)
Add Search Blacklist "_obligation_".



Ltac determ_tac LEMMA :=
  let tac := eauto in
  let x := rev_all ltac:(fun f => apply f) in
  let y := all ltac:(fun f => apply f) in
  first[
      exploit LEMMA; [x|y|]
    | exploit LEMMA; [tac|x|y|]
    | exploit LEMMA; [tac|tac|x|y|]
    | exploit LEMMA; [tac|tac|tac|x|y|]
    | exploit LEMMA; [tac|tac|tac|tac|x|y|]
    ];
  i; des; clarify.

(* TODO: if it is mature enough, move it to sflib & remove this file *)

Definition update_fst {A B C: Type} (f: A -> C) (ab: A * B): C * B := (f (fst ab), (snd ab)).

Definition update_snd {A B C: Type} (f: B -> C) (ab: A * B): A * C := ((fst ab), f (snd ab)).

Lemma dep_split_right
      (A B: Prop) (PA: A)
      (PB: <<LEFT: A>> -> B):
    <<SPLIT: A /\ B>>.
Proof. split; eauto. Qed.

Lemma dep_split_left
      (A B: Prop)
      (PA: <<RIGHT: B>> -> A)
      (PB: B):
    A /\ B.
Proof. split; eauto. Qed.

Lemma Forall_app A P (l0 l1: list A)
      (FORALL0: Forall P l0)
      (FORALL1: Forall P l1):
    Forall P (l0 ++ l1).
Proof. ginduction l0; i; ss. inv FORALL0. econs; eauto. Qed.

Global Program Instance incl_PreOrder {A}: PreOrder (@incl A).
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eauto. Qed.

(* is_Some & is_None? a bit harder to type *)
Definition is_some {X} (x: option X): bool :=
  match x with
  | Some _ => true
  | _ => false
  end.

Definition is_none {X} := negb <*> (@is_some X).

Hint Unfold is_some is_none.


Notation "x $" := ((proj1_sig x)) (at level 50, no associativity (* , only parsing *)).

Notation top1 := (fun _ => True).
Notation top2 := (fun _ _ => True).
Notation top3 := (fun _ _ _ => True).
Notation top4 := (fun _ _ _ _ => True).
Notation top5 := (fun _ _ _ _ _ => True).
Notation top6 := (fun _ _ _ _ _ _ => True).

Hint Unfold Basics.compose.


(* Note: not clos_refl_trans. That is not well-founded.. *)
Lemma well_founded_clos_trans
      index
      (order: index -> index -> Prop)
      (WF: well_founded order):
    <<WF: well_founded (clos_trans index order)>>.
Proof. hnf in WF. hnf. i. eapply Acc_clos_trans. eauto. Qed.

Lemma Forall2_impl
      X Y
      (xs: list X) (ys: list Y)
      (P Q: X -> Y -> Prop)
      (* (IMPL: all3 (P <3= Q)) *)
      (IMPL: (P <2= Q))
      (FORALL: Forall2 P xs ys):
    <<FORALL: Forall2 Q xs ys>>.
Proof. induction FORALL; econs; eauto. Qed.

Inductive Forall3 X Y Z (R: X -> Y -> Z -> Prop): list X -> list Y -> list Z -> Prop :=
| Forall3_nil: Forall3 R [] [] []
| Forall3_cons
    x y z xs ys zs
    (TAIL: Forall3 R xs ys zs):
    Forall3 R (x :: xs) (y :: ys) (z :: zs).

Lemma Forall3_impl
      X Y Z
      (xs: list X) (ys: list Y) (zs: list Z)
      (P Q: X -> Y -> Z -> Prop)
      (* (IMPL: all3 (P <3= Q)) *)
      (IMPL: (P <3= Q))
      (FORALL: Forall3 P xs ys zs):
    <<FORALL: Forall3 Q xs ys zs>>.
Proof. induction FORALL; econs; eauto. Qed.


Definition o_map A B (oa: option A) (f: A -> B): option B :=
  match oa with
  | Some a => Some (f a)
  | None => None
  end.

Definition o_join A (a: option (option A)): option A :=
  match a with
  | Some a => a
  | None => None
  end.

Definition o_bind A B (oa: option A) (f: A -> option B): option B := o_join (o_map oa f).
Hint Unfold o_map o_join o_bind.

Definition curry2 A B C (f: A -> B -> C): (A * B) -> C := fun ab => f (fst ab) (snd ab).

Definition o_bind2 A B C (oab: option (A * B)) (f: A -> B -> option C) : option C :=
o_join (o_map oab (curry2 f)).

(* Notation "o >>= f" := (o_bind o f) (at level 50, no associativity) : option_monad_scope. *)

(* Copied from Errors.v *)

Notation "'do' X <- A ; B" := (o_bind A (fun X => B))
 (at level 200, X ident, A at level 100, B at level 200)
 : o_monad_scope.


Notation "'do' ( X , Y ) <- A ; B" := (o_bind2 A (fun X Y => B))
 (at level 200, X ident, Y ident, A at level 100, B at level 200)
 : o_monad_scope.

Notation "'assertion' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200, only parsing)
  : o_monad_scope.

Open Scope o_monad_scope.

Lemma o_bind_ignore
      X Y
      (x: option X) (y: option Y):
    (do _ <- x ; y) = assertion(x) ; y.
Proof. des_ifs. Qed.

Ltac subst_locals := all ltac:(fun H => is_local_definition H; subst H).

Hint Unfold flip.

Notation "p -1 q" := (p /1\ ~1 q) (at level 50).
Notation "p -2 q" := (p /2\ ~2 q) (at level 50).
Notation "p -3 q" := (p /3\ ~3 q) (at level 50).
Notation "p -4 q" := (p /4\ ~4 q) (at level 50).

Tactic Notation "u" "in" hyp(H) := repeat (autounfold with * in H; cbn in H).
Tactic Notation "u" := repeat (autounfold with *; cbn).
Tactic Notation "u" "in" "*" := repeat (autounfold with * in *; cbn in *).

Lemma dependent_split_right
      (A B: Prop)
      (PA: A)
      (PB: <<HINTLEFT: A>> -> B):
    <<PAB: A /\ B>>.
Proof. eauto. Qed.

Lemma dependent_split_left
      (A B: Prop)
      (PA: <<HINTRIGHT: B>> -> A)
      (PB: B):
    <<PAB: A /\ B>>.
Proof. eauto. Qed.

Ltac dsplit_r := eapply dependent_split_right.
Ltac dsplit_l := eapply dependent_split_left.
Ltac dsplits :=
  repeat (let NAME := fresh "SPLITHINT" in try (dsplit_r; [|intro NAME])).

Locate des_sumbool.



Definition sumbool_to_bool {P Q: Prop} (a: {P} + {Q}) : bool := if a then true else false.

Coercion sumbool_to_bool: sumbool >-> bool.

Lemma sumbool_to_bool_true P Q (pq: { P } + { Q }): sumbool_to_bool pq = true -> P.
Proof. i. destruct pq; ss. Qed.

Lemma sumbool_to_bool_is_true P (p: { P } + { ~P }): P -> sumbool_to_bool p = true.
Proof. i. destruct p; ss. Qed.

Lemma sumbool_to_bool_is_false
      P
      (a: {P} + {~ P})
      (FALSE: ~ P):
    <<FALSE: sumbool_to_bool a = false>>.
Proof. unfold sumbool_to_bool. des_ifs. Qed.

Lemma sumbool_to_bool_false P Q (pq: { P } + { Q }): sumbool_to_bool pq = false -> Q.
Proof. intros. destruct pq; ss. Qed.

Ltac des_sumbool :=
  repeat
    (unfold Datatypes.is_true, is_true in *;
     match goal with
     | [ H: sumbool_to_bool ?x = true |- _ ] => apply sumbool_to_bool_true in H
     | [ H: sumbool_to_bool ?x = false |- _ ] => apply sumbool_to_bool_false in H
     | [ H: true = sumbool_to_bool ?x |- _ ] => symmetry in H; apply sumbool_to_bool_true in H
     | [ H: false = sumbool_to_bool ?x |- _ ] => symmetry in H; apply sumbool_to_bool_false in H

     | [ |- sumbool_to_bool ?x = true ] => apply sumbool_to_bool_is_true
     | [ |- sumbool_to_bool ?x = false ] => apply sumbool_to_bool_is_false
     | [ |- true = sumbool_to_bool ?x ] => symmetry; apply sumbool_to_bool_is_true
     | [ |- false = sumbool_to_bool ?x ] => symmetry; apply sumbool_to_bool_is_false
     end).

Ltac is_prop H :=
  let ty := type of H in
  match type of ty with
  | Prop => idtac
  | _ => fail 1
  end.

Ltac all_prop TAC := all ltac:(fun H => tryif is_prop H then TAC H else idtac).

Ltac all_prop_inv := all_prop inv.
(* TODO: infinite loop when inv-ing "a+b = c+d". "progress" tactic does not help here. *)
(* TODO: add all_once, which captures only current hypotheses and apply TAC *)

Ltac all_rewrite := all ltac:(fun H => rewrite_all H).

Definition bar_True: Type := True.
Global Opaque bar_True.
Ltac bar :=
  let NAME := fresh
                "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT" in
  assert(NAME: bar_True) by ss.

Ltac clear_until id :=
  on_last_hyp ltac:(fun id' => match id' with
                               | id => idtac
                               | _ => clear id'; clear_until id
                               end).

Ltac clear_until_bar :=
  on_last_hyp ltac:(fun id' => match (type of id') with
                               | bar_True => idtac
                               | _ => clear id'; clear_until_bar
                               end).

Goal True -> True -> False.
  intro. bar. intro. clear_until H0. clear_until H. Undo 2. clear_until_bar. clear_tac.
Abort.



Definition aof_true: Type := True.
Global Opaque aof_true.

Ltac place_bar name :=
  first [ on_last_hyp ltac:(fun H => revert H; place_bar name; intros H) | assert(name: aof_true) by constructor].

Ltac all_once_fast TAC :=
  generalize (I: aof_true);
  let name := fresh "bar" in
  place_bar name; revert_until name;
  repeat
    match goal with
    | [ |- aof_true -> _ ] => fail 1
    | _ => intro; on_last_hyp TAC
    end;
  intro; on_last_hyp ltac:(fun H => clear H);
  clear name.

Goal forall (a b c d e: bool) f,
    (negb true = false) -> (* IT SHOULD NOT RUN INF LOOP *)
    (negb false = true) ->
    (negb a = true) ->
    (negb b = true) ->
    (negb c = true) ->
    True -> (* SHOULD IGNORE THIS *)
    (negb d = true) ->
    (negb e = true) ->
    (0 :: 2 :: nil = f) -> (* SHOULD IGNORE THIS *)
    (negb (true && false) = true) -> True -> False.
Proof.
  i. revert H9. all_once_fast ltac:(fun H => try apply negb_true_iff in H).
Abort.

Ltac spc H :=
  let TAC := ss; eauto in
  let ty := type of H in
  match eval hnf in ty with
  | forall (a: ?A), _ =>
    (* let A := (eval compute in _A) in *)
    match goal with
    | [a0: A, a1: A, a2: A, a3: A, a4: A, a5: A |- _] => fail 2 "6 candidates!" a0 "," a1 "," a2 "," a3 "," a4 "," a5
    | [a0: A, a1: A, a2: A, a3: A, a4: A |- _] => fail 2 "5 candidates!" a0 "," a1 "," a2 "," a3 "," a4
    | [a0: A, a1: A, a2: A, a3: A |- _] => fail 2 "4 candidates!" a0 "," a1 "," a2 "," a3
    | [a0: A, a1: A, a2: A |- _] => fail 2 "3 candidates!" a0 "," a1 "," a2
    | [a0: A, a1: A |- _] => fail 2 "2 candidates!" a0 "," a1
    | [a0: A |- _] => specialize (H a0)
    | _ =>
      tryif is_prop A
      then
        let name := fresh in
        assert(name: A) by TAC; specialize (H name); clear name
      else
        fail 2 "No specialization possible!"
    end
  | _ => fail 1 "Nothing to specialize!"
  end.

Ltac spcN n H :=
  let TAC := ss; eauto in
  let ty := type of H in
  match type of n with
  | Z => idtac
  | _ => fail "second argument should be 'Z'"
  end;
  match eval hnf in ty with
  | forall (a: ?A), _ =>
    (* let A := (eval compute in _A) in *)
    match goal with
    | [a0: A, a1: A, a2: A, a3: A, a4: A, a5: A |- _] =>
      match n with
      | - 5 => specialize (H a1)
      | - 4 => specialize (H a2)
      | - 3 => specialize (H a3)
      | - 2 => specialize (H a4)
      | - 1 => specialize (H a5)
      | 0%Z => specialize (H a0)
      | 1%Z => specialize (H a1)
      | 2%Z => specialize (H a2)
      | 3%Z => specialize (H a3)
      | 4%Z => specialize (H a4)
      | 5%Z => specialize (H a5)
      | _ => fail 2 "6 candidates!" a0 "," a1 "," a2 "," a3 "," a4 "," a5
      end
    | [a0: A, a1: A, a2: A, a3: A, a4: A |- _] =>
      match n with
      | - 4 => specialize (H a1)
      | - 3 => specialize (H a2)
      | - 2 => specialize (H a3)
      | - 1 => specialize (H a4)
      | 0%Z => specialize (H a0)
      | 1%Z => specialize (H a1)
      | 2%Z => specialize (H a2)
      | 3%Z => specialize (H a3)
      | 4%Z => specialize (H a4)
      | _ => fail 2 "5 candidates!" a0 "," a1 "," a2 "," a3 "," a4
      end
    | [a0: A, a1: A, a2: A, a3: A |- _] =>
      match n with
      | - 3 => specialize (H a1)
      | - 2 => specialize (H a2)
      | - 1 => specialize (H a3)
      | 0%Z => specialize (H a0)
      | 1%Z => specialize (H a1)
      | 2%Z => specialize (H a2)
      | 3%Z => specialize (H a3)
      | _ => fail 2 "4 candidates!" a0 "," a1 "," a2 "," a3
      end
    | [a0: A, a1: A, a2: A |- _] =>
      match n with
      | - 2 => specialize (H a1)
      | - 1 => specialize (H a2)
      | 0%Z => specialize (H a0)
      | 1%Z => specialize (H a1)
      | 2%Z => specialize (H a2)
      | _ => fail 2 "3 candidates!" a0 "," a1 "," a2
      end
    | [a0: A, a1: A |- _] =>
      match n with
      | - 1 => specialize (H a1)
      | 0%Z => specialize (H a0)
      | 1%Z => specialize (H a1)
      | _ => fail 2 "2 candidates!" a0 "," a1
      end
    | [a0: A |- _] => specialize (H a0)
    | _ =>
      tryif is_prop A
      then
        let name := fresh in
        assert(name: A) by TAC; specialize (H name); clear name
      else
        fail 2 "No specialization possible!"
    end
  | _ => fail 1 "Nothing to specialize!"
  end.

Goal let my_nat := nat in
     let my_f := my_nat -> Prop in
     forall (f: my_f) (g: nat -> Prop) (x: nat) (y: my_nat), False.
  i. spc f. spc g.
Abort.

Lemma map_ext_strong
      X Y (f g: X -> Y) xs
      (EXT: forall x (IN: In x xs), f x = g x):
    map f xs = map g xs.
Proof.
  ginduction xs; ii; ss. exploit EXT; eauto. i; des.
  f_equal; ss. eapply IHxs; eauto.
Qed.

(* copied from : https://robbertkrebbers.nl/research/ch2o/tactics.html *)
Hint Extern 998 (_ = _) => f_equal : f_equal.
Hint Extern 999 => congruence : congruence.
Hint Extern 1000 => lia : lia.



Ltac inv_all_once := all_once_fast ltac:(fun H => try inv H).
Ltac apply_all_once LEMMA :=  all_once_fast ltac:(fun H => try apply LEMMA in H).

Lemma find_map
      X Y (f: Y -> bool) (x2y: X -> Y) xs:
    find f (map x2y xs) = o_map (find (f <*> x2y) xs) x2y.
Proof. u. ginduction xs; ii; ss. des_ifs; ss. Qed.

Ltac revert_until_bar :=
  on_last_hyp ltac:(fun id' => match (type of id') with
                               | bar_True => idtac
                               | _ => revert id'; revert_until_bar
                               end).

(* Ltac folder := all_once_fast ltac:(fun H => try (is_local_definition H; fold_all H)). *)
Ltac folder :=
  repeat multimatch goal with
         | [ H: _ |- _ ] => is_local_definition H; fold_all H
         end.

(* copied from promising/lib/Basic.v *)

Ltac refl := reflexivity.
Ltac etrans := etransitivity.
Ltac congr := congruence.

Notation rtc := (clos_refl_trans_1n _). (* reflexive transitive closure *)
Notation rc := (clos_refl _). (* reflexive transitive closure *)
Notation tc := (clos_trans _). (* transitive closure *)
Hint Immediate rt1n_refl rt1n_trans t_step.

Program Instance rtc_PreOrder A (R:A -> A -> Prop): PreOrder (rtc R).
Next Obligation.
  ii. revert H0. induction H; auto. i. exploit IHclos_refl_trans_1n; eauto.
Qed.

Lemma rtc_tail A R
      (a1 a3:A)
      (REL: rtc R a1 a3):
  (exists a2, rtc R a1 a2 /\ R a2 a3) \/
  (a1 = a3).
Proof.
  induction REL; auto. des; subst; left; eexists; splits; [|eauto| | eauto]; econs; eauto.
Qed.

Lemma rtc_implies A (R1 R2: A -> A -> Prop)
      (IMPL: R1 <2= R2):
  rtc R1 <2= rtc R2.
Proof.
  ii. induction PR; eauto. etrans; [|eauto]. econs 2; [|econs 1]. apply IMPL. auto.
Qed.

Lemma rtc_refl
      A R (a b:A)
      (EQ: a = b):
  rtc R a b.
Proof. subst. econs. Qed.

Lemma rtc_n1
      A R (a b c:A)
      (AB: rtc R a b)
      (BC: R b c):
  rtc R a c.
Proof. etrans; eauto. econs 2; eauto. Qed.

Lemma rtc_reverse
      A R (a b:A)
      (RTC: rtc R a b):
  rtc (fun x y => R y x) b a.
Proof. induction RTC; eauto. etrans; eauto. econs 2; eauto. Qed.

Lemma rtc_once
      A (R: A -> A -> Prop) a b
      (ONCE: R a b):
    rtc R a b.
Proof. econs; eauto. Qed.

Lemma Forall2_length
      X Y (P: X -> Y -> Prop) xs ys
      (FORALL2: Forall2 P xs ys):
    length xs = length ys.
Proof. ginduction FORALL2; ii; ss. lia. Qed.

Ltac hexpl_aux H NAME :=
  let n := fresh NAME in
  first[hexploit H; eauto; check_safe; repeat intro n; des].
Tactic Notation "hexpl" constr(H) := hexpl_aux H H.
(* Tactic Notation "hexpl" constr(H) tactic(TAC) := hexpl_aux H TAC. *)
Tactic Notation "hexpl" constr(H) ident(NAME) := hexpl_aux H NAME.

(* 0 goal *)
Goal forall (mytt: unit) (H: unit -> False), False.
  i. hexpl H.
Qed.

(* 1 goal *)
Goal forall (H: nat -> False), False.
  i. hexpl H.
Abort.

Goal forall (H: nat -> nat -> False), False.
  i. Fail hexpl H.
Abort.

(* name *)
Goal forall (mytt: unit) (HH: unit -> (True -> True /\ True)), False.
  i. hexpl HH ABC. hexpl HH.
Abort.

Hint Extern 997 => lia : lia.

Hint Rewrite
     Z.add_0_l Z.add_0_r Z.add_assoc Z.add_simpl_l Z.add_simpl_r Z.add_opp_r Z.add_opp_l
     Z.mul_0_l Z.mul_0_r Z.mul_assoc
     Z.sub_0_r Z.sub_diag Z.sub_simpl_l Z.sub_simpl_r Z.sub_0_l
     Z.div_0_l Zdiv_0_r Z.div_1_r
     Z.mod_1_r Z.mod_0_l Z.mod_same Z.mod_mul Z.mod_mod
     Z.sub_add
  : zsimpl.

Ltac zsimpl := repeat autorewrite with zsimpl in *.

Ltac rp := first [erewrite f_equal8|
                  erewrite f_equal7|
                  erewrite f_equal6|
                  erewrite f_equal5|
                  erewrite f_equal4|
                  erewrite f_equal3|
                  erewrite f_equal2|
                  erewrite f_equal|
                  fail].

Ltac align_bool :=
  (repeat match goal with
          | [ H: true <> true |- _ ] => tauto
          | [ H: false <> false |- _ ] => tauto
          | [ H: true <> _ |- _ ] => symmetry in H
          | [ H: false <> _ |- _ ] => symmetry in H
          | [ H: _ <> true |- _ ] => apply not_true_is_false in H
          | [ H: _ <> false |- _ ] => apply not_false_is_true in H
          end).
Ltac simpl_bool := unfold Datatypes.is_true in *; unfold is_true in *; autorewrite with simpl_bool in *.
Ltac bsimpl := simpl_bool.

Definition range (lo hi: Z): Z -> Prop := fun x => lo <= x < hi. (* TODO: Use Notation instead *)
Hint Unfold range.

Ltac sym := symmetry.
Tactic Notation "sym" "in" hyp(H) := symmetry in H.

Ltac eapply_all_once LEMMA :=
  all_once_fast ltac:(fun H => try eapply LEMMA in H; try eassumption; check_safe).

Ltac Nsimpl := all_once_fast ltac:(fun H => try apply NNPP in H; try apply not_and_or in H; try apply not_or_and in H).

Ltac hexploit1 H :=
  match goal with
  | [ H: ?A -> ?B |- _ ] =>
    apply (@mp B); [apply H|clear H; intro H]
  end.

Lemma rev_nil
      X (xs: list X)
      (NIL: rev xs = []):
    xs = [].
Proof.
  generalize (f_equal (@length _) NIL). i. ss. destruct xs; ss. rewrite app_length in *. ss. lia.
Qed.

Fixpoint last_opt X (xs: list X): option X :=
  match xs with
  | [] => None
  | [hd] => Some hd
  | hd :: tl => last_opt tl
  end.

Lemma last_none
      X (xs: list X)
      (NONE: last_opt xs = None):
    xs = [].
Proof. ginduction xs; ii; ss. des_ifs. spc IHxs. ss. Qed.

Lemma last_some
      X (xs: list X) x
      (SOME: last_opt xs = Some x):
    exists hds, xs = hds ++ [x].
Proof.
  ginduction xs; ii; ss. des_ifs.
  { exists nil. ss. }
  exploit IHxs; eauto. i; des. rewrite x2. exists (a :: hds). ss.
Qed.

Fixpoint zip X Y Z (f: X -> Y -> Z) (xs: list X) (ys: list Y): list Z :=
  match xs, ys with
  | xhd :: xtl, yhd :: ytl => f xhd yhd :: zip f xtl ytl
  | _, _ => []
  end.

Lemma zip_length
      X Y Z (f: X -> Y -> Z) xs ys:
    length (zip f xs ys) = min (length xs) (length ys).
Proof. ginduction xs; ii; ss. des_ifs. ss. rewrite IHxs. lia. Qed.

Lemma in_zip_iff
      X Y Z (f: X -> Y -> Z) xs ys z:
    (<<ZIP: In z (zip f xs ys)>>)
    <-> (exists x y, <<F: f x y = z>> /\ exists n, <<X: nth_error xs n = Some x>> /\ <<Y: nth_error ys n = Some y>>).
Proof.
  split; ii.
  - ginduction xs; ii; ss. des_ifs. ss. des; ss.
    + esplits; eauto; try instantiate (1 := 0%nat); ss.
    + exploit IHxs; eauto. i; des. esplits; eauto; try instantiate (1:= (1+n)%nat); ss.
  - des. ginduction n; ii; ss.
    { des_ifs. ss. left; ss. }
    des_ifs. ss. exploit (@IHn _ _ _ f); eauto.
Qed.

Global Opaque Z.mul.

Lemma unit_ord_wf: well_founded (bot2: unit -> unit -> Prop).
Proof. ii. induction a; ii; ss. Qed.

Ltac et:= eauto.

Require Import Program.

Lemma f_equal_h
      X1 X2 Y1 Y2 (f1: X1 -> Y1) (f2: X2 -> Y2) x1 x2
      (TYPX: X1 = X2)
      (FUNC: f1 ~= f2)
      (ARG: x1 ~= x2)
      (TYPY: Y1 = Y2): (* Do we need this? *)
    f1 x1 ~= f2 x2.
Proof. subst. eapply JMeq_eq in FUNC. subst. ss. Qed.

Lemma f_equal_hr
      X1 X2 Y (f1: X1 -> Y) (f2: X2 -> Y) x1 x2
      (FUNC: f1 ~= f2)
      (TYP: X1 = X2)
      (ARG: x1 ~= x2):
    f1 x1 = f2 x2.
Proof. eapply JMeq_eq. eapply f_equal_h; eauto. Qed.

Lemma f_equal_rh
      X Y1 Y2 (f1: X -> Y1) (f2: X -> Y2) x
      (FUNC: f1 ~= f2)
      (TYP: Y1 = Y2):
    f1 x ~= f2 x.
Proof. eapply f_equal_h; eauto. Qed.

Lemma cons_app
      X xhd (xtl: list X):
    xhd :: xtl = [xhd] ++ xtl.
Proof. ss. Qed.

Lemma list_map_injective A B (f: A -> B)
      (INJECTIVE: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
      l0 l1
      (LEQ: map f l0 = map f l1):
    l0 = l1.
Proof.
  revert l1 LEQ. induction l0; i; ss; destruct l1; ss. inv LEQ. f_equal; eauto.
Qed.

Lemma Forall_in_map A B al (R: B -> Prop) (f: A -> B)
      (RMAP: forall a (IN: In a al), R (f a)):
    Forall R (map f al).
Proof. induction al; econs; ss; eauto. Qed.

Lemma Forall_map A B la (R: B -> Prop) (f: A -> B)
      (RMAP: forall a, R (f a)):
    Forall R (map f la).
Proof. induction la; econs; ss. Qed.

Lemma f_hequal A (B : A -> Type) (f : forall a, B a)
      a1 a2 (EQ : a1 = a2):
    f a1 ~= f a2.
Proof. destruct EQ. econs. Qed.

Ltac uo := unfold o_bind, o_bind2, o_map, o_join in *.

Lemma some_injective
      X (x0 x1: X)
      (EQ: Some x0 = Some x1):
    x0 = x1.
Proof. injection EQ. auto. Qed.

Ltac align_opt :=
  repeat
    match goal with
    (* remove trivial things *)
    | H: Some ?x = Some ?y |- _ => rewrite some_injective in H
    | H: Some _ = None |- _ => by (inversion H)
    | H: None = Some _ |- _ => by (inversion H)
    | H: None = None |- _ => clear H
    (* align *)
    | H: Some _ = ?x |- _ => symmetry in H
    | H: None = ?x |- _ => symmetry in H
    end.
(* Ltac clarify0 := repeat (align_opt; progress clarify). *)

Fixpoint list_diff X (dec: (forall x0 x1, {x0 = x1} + {x0 <> x1})) (xs0 xs1: list X): list X :=
  match xs0 with
  | [] => []
  | hd :: tl =>
    if in_dec dec hd xs1
    then list_diff dec tl xs1
    else hd :: list_diff dec tl xs1
  end.

Lemma list_diff_spec
      X dec (xs0 xs1 xs2: list X)
      (DIFF: list_diff dec xs0 xs1 = xs2):
    <<SPEC: forall x0, In x0 xs2 <-> (In x0 xs0 /\ ~ In x0 xs1)>>.
Proof.
  subst. split; i.
  - ginduction xs0; ii; des; ss. des_ifs.
    { exploit IHxs0; et. i; des. esplits; et. }
    ss. des; clarify.
    { tauto. }
    exploit IHxs0; et. i; des. esplits; et.
  - ginduction xs0; ii; des; ss. des; clarify; des_ifs; ss; try tauto; exploit IHxs0; et.
Qed.

Fixpoint last_option X (xs: list X): option X :=
  match xs with
  | [] => None
  | hd :: nil => Some hd
  | hd :: tl => last_option tl
  end.
Lemma not_ex_all_not
      U (P: U -> Prop)
      (NEX: ~ (exists n : U, P n)):
    <<NALL: forall n : U, ~ P n>>.
Proof. eauto. Qed.

(* Remark: if econs/econsr gives different goal, at least 2 econs is possible *)
Ltac econsr :=
  first
    [ econstructor 30
     |econstructor 29
     |econstructor 28
     |econstructor 27
     |econstructor 26
     |econstructor 25
     |econstructor 24
     |econstructor 23
     |econstructor 22
     |econstructor 21
     |econstructor 20
     |econstructor 19
     |econstructor 18
     |econstructor 17
     |econstructor 16
     |econstructor 15
     |econstructor 14
     |econstructor 13
     |econstructor 12
     |econstructor 11
     |econstructor 10
     |econstructor  9
     |econstructor  8
     |econstructor  7
     |econstructor  6
     |econstructor  5
     |econstructor  4
     |econstructor  3
     |econstructor  2
     |econstructor  1].

Ltac it TERM := instantiate (1:=TERM).
Ltac itl TERM :=
  first[ instantiate (10:=TERM)|
         instantiate (9:=TERM)|
         instantiate (8:=TERM)|
         instantiate (7:=TERM)|
         instantiate (6:=TERM)|
         instantiate (5:=TERM)|
         instantiate (4:=TERM)|
         instantiate (3:=TERM)|
         instantiate (2:=TERM)|
         instantiate (1:=TERM)|
         fail].

Ltac swapname NAME1 NAME2 :=
  let tmp := fresh "TMP" in
  rename NAME1 into tmp; rename NAME2 into NAME1; idtac NAME1; rename tmp into NAME2
.

Global Program Instance top2_PreOrder X: PreOrder (top2: X -> X -> Prop).

Lemma app_eq_inv
      A (x0 x1 y0 y1: list A)
      (EQ: x0 ++ x1 = y0 ++ y1)
      (LEN: (length x0) = (length y0)):
    x0 = y0 /\ x1 = y1.
Proof.
  ginduction x0; ii; ss.
  { destruct y0; ss. }
  destruct y0; ss. clarify. exploit IHx0; eauto. i; des. clarify.
Qed.

Lemma pos_elim_succ: forall p,
    <<ONE: p = 1%positive>> \/
    <<SUCC: exists q, (Pos.succ q) = p>>.
Proof. i. hexploit (Pos.succ_pred_or p); eauto. i; des; ss; eauto. Qed.

Section FLIPS.

Definition flip2 A B C D: (A -> B -> C -> D) -> A -> C -> B -> D. intros; eauto. Defined.
Definition flip3 A B C D E: (A -> B -> C -> D -> E) -> A -> B -> D -> C -> E. intros; eauto. Defined.
Definition flip4 A B C D E F: (A -> B -> C -> D -> E -> F) -> A -> B -> C -> E -> D -> F. intros; eauto. Defined.

Variable A B C D: Type.
Variable f: A -> B -> C -> D.

Let put_dummy_arg_without_filp A DUMMY B: (A -> B) -> (A -> DUMMY -> B) := fun f => (fun a _ => f a).
Let put_dummy_arg1 A DUMMY B: (A -> B) -> (A -> DUMMY -> B) := fun f => (flip (fun _ => f)).
Let put_dummy_arg21 A DUMMY B C: (A -> B -> C) -> (A -> DUMMY -> B -> C) := fun f => (flip (fun _ => f)).
Let put_dummy_arg22 A B DUMMY C: (A -> B -> C) -> (A -> B -> DUMMY -> C) :=
  fun f => (flip2 (flip (fun _ => f))).

End FLIPS.
Hint Unfold flip2 flip3 flip4.

Definition DUMMY_PROP := True.
Hint Unfold DUMMY_PROP.

Lemma firstn_S
      (A: Type) (l: list A) n:
      (le (Datatypes.length l) n /\ firstn (n + 1) l = firstn n l)
    \/ (lt n (Datatypes.length l) /\ exists x, firstn (n + 1) l = (firstn n l) ++ [x]).
Proof.
  ginduction l; i; try by (left; do 2 rewrite firstn_nil; split; ss; lia). destruct n.
  { right. ss. split; try lia. eauto. }
  specialize (IHl n). ss. des.
  - left. split; try lia. rewrite IHl0. ss.
  - right. split; try lia. rewrite IHl0. eauto.
Qed.

Lemma map_firstn
      (A B: Type) (l: list A) (f: A -> B) n:
    map f (firstn n l) = firstn n (map f l).
Proof.
  ginduction l; ss; i.
  { ss. do 2 rewrite firstn_nil. ss. }
  destruct n; ss. rewrite IHl. ss.
Qed.

Lemma Forall2_apply_Forall2 A B C D (f: A -> C) (g : B -> D)
      (P: A -> B -> Prop) (Q: C -> D -> Prop)
      la lb
      (FORALL: Forall2 P la lb)
      (IMPLY: forall a b (INA: In a la) (INB: In b lb),
          P a b -> Q (f a) (g b)):
    Forall2 Q (map f la) (map g lb).
Proof.
  ginduction la; ss; i; inv FORALL; ss. econs; eauto.
Qed.

Ltac des_u := match goal with | [ a: unit |- _ ] => destruct a end.

Definition mapi_aux A B (f: nat -> A -> B) :=
  let fix rec (cur : nat) (la : list A) {struct la}: list B :=
      match la with
      | [] => []
      | hd :: tl => f cur hd :: rec (S cur) tl
      end
  in rec.

Definition mapi A B (f: nat -> A -> B) (la: list A): list B :=
  mapi_aux f (0%nat) la.

Lemma in_mapi_aux_iff
      A B (f: nat -> A -> B) la b
  :
    forall m,
      In b (mapi_aux f m la) <->
      (exists idx a, f (m + idx)%nat a = b /\ nth_error la idx = Some a)
.
Proof.
  ginduction la; split; ii; ss; des; firstorder (subst; auto).
  - destruct idx; ss.
  - exists 0%nat. rewrite Nat.add_0_r. esplits; eauto.
  - exploit IHla; eauto. intros [T _]. exploit T; eauto. i; des. esplits; eauto.
    { rp; eauto. f_equal. instantiate (1:= (S idx%nat)). lia. }
    ss.
  - destruct idx; ss; clarify.
    { left. f_equal. lia. }
    right. eapply IHla; eauto. esplits; eauto.
    { rp; eauto. f_equal. lia. }
Qed.

(* NOTE: If you give name << >>, rewrite tactic does not work... *)
(* TODO: FIX IT *)
Lemma in_mapi_iff
      A B (f: nat -> A -> B) la b
  :
    (* (<<IN: In b (mapi f la)>>) <-> *)
    (* (<<NTH: (exists idx a, f idx a = b /\ nth_error la idx = Some a)>>) *)
    In b (mapi f la) <->
    (exists idx a, f (idx) a = b /\ nth_error la idx = Some a)
.
Proof.
  eapply in_mapi_aux_iff.
Qed.

Lemma nth_error_mapi_aux_iff
      A B (f: nat -> A -> B) la b
  :
    forall idx m,
      nth_error (mapi_aux f m la) idx = Some b <->
      (exists a, f (m + idx)%nat a = b /\ nth_error la idx = Some a)
.
Proof.
  ginduction la; split; ii; ss; des; firstorder (subst; auto).
  - destruct idx; ss.
  - destruct idx; ss.
  - destruct idx; ss; clarify.
    + esplits; eauto. f_equal; lia.
    + exploit IHla; eauto. intros [T _]. eapply T in H. des. clarify.
      esplits; eauto. ss. f_equal; lia.
  - destruct idx; ss; clarify.
    { repeat f_equal; lia. }
    exploit IHla; eauto. intros [_ T]. exploit T; eauto. intro Q; des.
    replace (m + S idx)%nat with (S m + idx)%nat by lia.
    rewrite Q. ss.
Qed.

Lemma nth_error_mapi_iff
      A B (f: nat -> A -> B) la b
  :
    forall idx,
      nth_error (mapi f la) idx = Some b <->
      (exists a, f (idx)%nat a = b /\ nth_error la idx = Some a)
.
Proof.
  split; ii; des.
  - eapply nth_error_mapi_aux_iff in H; eauto.
  - eapply nth_error_mapi_aux_iff; eauto.
Qed.

Lemma mapi_aux_length
      A B (f: nat -> A -> B) m la
  :
    <<LEN: length (mapi_aux f m la) = length la>>
.
Proof.
  ginduction la; ii; ss.
  erewrite IHla; eauto.
Qed.

Lemma nth_error_mapi_none_aux_iff
      A B  (f : nat -> A -> B) la idx m
  :
    <<NTH: nth_error (mapi_aux f m la) idx = None>> <->
           <<LEN: (length la <= idx)%nat>>
.
Proof.
  split; i.
  - ginduction la; ii; ss; des.
    + destruct idx; ii; ss. r. lia.
    + destruct idx; ii; ss. r. exploit IHla; eauto. i; des. lia.
  - ginduction la; ii; ss; des.
    + destruct idx; ii; ss.
    + destruct idx; ii; ss. { lia. } eapply IHla; eauto. r. lia.
Qed.

Definition option_dec X (dec: forall x0 x1: X, {x0 = x1} + {x0 <> x1})
           (x0 x1: option X): {x0 = x1} + {x0 <> x1}
.
  decide equality.
Defined.

Fixpoint filter_map A B (f: A -> option B) (l: list A): list B :=
  match l with
  | [] => []
  | hd :: tl =>
    match (f hd) with
    | Some b => b :: (filter_map f tl)
    | _ => filter_map f tl
    end
  end
.

Lemma in_filter_map_iff
      X Y (f: X -> option Y) xs y
  :
    <<IN: In y (filter_map f xs)>> <-> (exists x, <<F: f x = Some y>> /\ <<IN: In x xs>>)
.
Proof.
  split; ii.
  - ginduction xs; ii; ss. des_ifs; ss; des; clarify; eauto.
    + exploit IHxs; eauto. i; des. eauto.
    + exploit IHxs; eauto. i; des. eauto.
  - des. ginduction xs; ii; ss. des_ifs; ss; des; clarify; eauto.
    exploit (IHxs _ f y x); eauto.
Qed.

Lemma nodup_length
      X (xs: list X) x_dec
  :
    <<LEN: (length (nodup x_dec xs) <= length (xs))%nat>>
.
Proof.
  r.
  ginduction xs; ii; ss. exploit IHxs; et. i; des. des_ifs; ss; try rewrite x0; try lia.
Qed.

Fixpoint snoc X (xs: list X) (x: X): list X :=
  match xs with
  | [] => [x]
  | hd :: tl => hd :: snoc tl x
  end
.

Lemma elim_snoc
      X (xs: list X)
  :
    <<NIL: xs = []>> \/ exists lt dh, <<SNOC: xs = snoc lt dh>>
.
Proof.
  ginduction xs; ii; ss; et.
  des; clarify; et.
  - right. exists nil, a. ss.
  - right. exists (a :: lt), dh. ss.
Qed.

Lemma rev_snoc
      X (x: X) lt
  :
    <<EQ: rev (snoc lt x) = x :: rev lt>>
.
Proof.
  ginduction lt; ii; ss.
  erewrite IHlt; et.
Qed.

Lemma func_app
      X Y (f: X -> Y)
      x0 x1
      (EQ: x0 = x1)
  :
    <<EQ: f x0 = f x1>>
.
Proof. clarify. Qed.
Arguments func_app [_] [_].

Lemma snoc_length
      X (x: X) lt
  :
    <<LEN: (length (snoc lt x) = length lt + 1)%nat>>
.
Proof.
  ginduction lt; ii; ss. erewrite IHlt; et.
Qed.

Lemma rev_cons
      X (xs: list X) x tl
      (REV: rev xs = x :: tl)
  :
    (<<NTH: nth_error xs (Datatypes.length xs - 1) = Some x>>)
.
Proof.
  ginduction xs; ii; ss.
  { generalize (elim_snoc xs); intro T.
    des; clarify.
    - ss. clarify.
    - rewrite rev_snoc in *; ss. clarify.
      exploit IHxs; et. i; des.
      rewrite snoc_length in *. destruct lt; ss. rewrite Nat.sub_0_r in *; ss.
  }
Qed.

(* TODO: Coqlib? *)
Lemma nodup_app_l A (l0 l1: list A)
      (ND: NoDup (l0 ++ l1))
  :
    NoDup l0.
Proof.
  induction l0.
  { econs. }
  ss. inv ND. econs; et.
  ii. eapply H1. eapply List.in_or_app. auto.
Qed.

Lemma nodup_app_r A (l0 l1: list A)
      (ND: NoDup (l0 ++ l1))
  :
    NoDup l1.
Proof.
  induction l0; ss. inv ND. auto.
Qed.

Lemma nodup_comm A (l0 l1: list A)
      (NODUP: NoDup (l0 ++ l1))
  :
    NoDup (l1 ++ l0).
Proof.
  eapply Permutation_NoDup; [|et].
  eapply Permutation_app_comm.
Qed.

Lemma NoDup_snoc
      X (x: X) xs
      (NIN: ~In x xs)
      (NDUP: NoDup xs)
  :
    <<NDUP: NoDup (xs ++ [x])>>
.
Proof.
  ginduction xs; ii; ss.
  - econs; et.
  - apply not_or_and in NIN. des.
    eapply NoDup_cons_iff in NDUP; des; ss.
    econs; et.
    + rewrite in_app_iff. apply and_not_or. esplits; et.
      * ss. ii; des; clarify.
    + eapply IHxs; et.
Qed.

Lemma NoDup_rev
      X (xs: list X)
      (UNIQ: NoDup xs)
  :
    <<UNIQ: NoDup (rev xs)>>
.
Proof.
  ginduction xs; ii; ss.
  inv UNIQ. eapply IHxs in H2.
  eapply NoDup_snoc; et. rewrite <- in_rev. ss.
Qed.

Lemma NoDup_app_disjoint A (l0 l1: list A) (NODUP: NoDup (l0 ++ l1))
  :
    forall a (IN0: List.In a l0) (IN1: List.In a l1), False.
Proof.
  revert NODUP. induction l0; et. i. ss. des; ss.
  { subst. inv NODUP. eapply H1. eapply in_or_app. auto. }
  { eapply IHl0; et. inv NODUP. ss. }
Qed.

Lemma map_ext
      A B
      (f g : A -> B)
      l
      (EQ: forall a (IN: In a l), <<EQ: f a = g a>>)
  :
    map f l = map g l
.
Proof.
  ginduction l; ii; ss.
  exploit EQ; et. i; des. erewrite IHl; et. congruence.
Qed.

Lemma filter_map_none
      X Y (f: X -> option Y) xs
      (NONE: forall x (IN: In x xs), f x = None)
  :
    <<NIL: filter_map f xs = []>>
.
Proof.
  clear - xs NONE. ginduction xs; ii; ss. exploit IHxs; et. intro T. rewrite T. des_ifs.
  exploit NONE; et. i; clarify.
Qed.

Lemma filter_map_app
      X Y xs0 xs1 (f: X -> option Y)
  :
    <<EQ: (filter_map f (xs0 ++ xs1)) = (filter_map f xs0) ++ (filter_map f xs1)>>
.
Proof.
  ginduction xs0; ii; ss.
  des_ifs. rewrite IHxs0. ss.
Qed.

Lemma filter_map_rev
      X Y xs (f: X -> option Y)
  :
    <<EQ: rev (filter_map f xs) = filter_map f (rev xs)>>
.
Proof.
  ginduction xs; ii; ss. des_ifs.
  - ss. rewrite IHxs; et. rewrite filter_map_app; ss. des_ifs.
  - ss. rewrite IHxs; et. rewrite filter_map_app; ss. des_ifs. rewrite app_nil_r. ss.
Qed.

Lemma nth_error_nth
      X
      (xs: list X) n x
      (NTH: nth_error xs n = Some x)
  :
    forall d, nth n xs d = x
.
Proof.
  ginduction xs; ii; ss; des_ifs; ss; clarify.
  exploit IHxs; eauto.
Qed.

Lemma prop_ext_rev
      A B
      (EQ: A = B)
  :
    A <-> B
.
Proof. clarify. Qed.

Lemma func_ext_rev
      A B
      (a: A)
      (f g: A -> B)
      (EQ: f = g)
  :
    f a = g a
.
Proof.
  clarify.
Qed.

(*** TODO: move to CoqlibC ***)
Lemma NoDup_inj_aux
      X Y (f: X -> Y) xs
      (NODUP: NoDup (map f xs))
      x0 x1
      (NEQ: x0 <> x1)
      (IN0: In x0 xs)
      (IN1: In x1 xs)
  :
    f x0 <> f x1
.
Proof.
  ginduction xs; i; ss.
  inv NODUP. des; clarify; et.
  - intro T. rewrite <- T in *. eapply H1. erewrite in_map_iff. eauto.
  - intro T. rewrite T in *. eapply H1. erewrite in_map_iff. eauto.
Qed.

Ltac fold_not :=
  repeat
    multimatch goal with
    | H: context [?P -> False] |- _ => fold (~ P) in H
    | |- context [?P -> False] => fold (~ P)
    end
.
Goal (True -> False) -> (True -> False -> False) -> (True -> False).
  intros T U. fold_not.
Abort.

Require Import Classical_Pred_Type.

Lemma not_and_or_strong
      P Q
      (H: (~ (P /\ Q)))
  :
    ((Q /\ ~ P) \/  ~Q)
.
Proof.
  apply not_and_or in H.
  destruct (classic Q); et.
  des; clarify; et.
Qed.

Lemma NNPP_rev
      (P: Prop)
      (p: P)
  :
    ~ ~ P
.
Proof. ii. eauto. Qed.

Ltac Psimpl_ :=
  match goal with
  | [ H: ~ ~ ?P |- _ ] => apply NNPP in H
  | [ H: ~ (NW (fun _ => ~ ?P)) |- _ ] => apply NNPP in H
  | [ |- ~ ~ ?P ] => apply NNPP_rev
  | [ H: (~?P -> ?P) |- _ ] => apply Peirce in H
  | [ H: ~ (?P -> ?Q) |- _ ] => apply imply_to_and in H
  | [ |- ~?P \/ ~?Q ] => apply imply_to_or
  (* Parameter or_to_imply : forall P Q : Prop, ~ P \/ Q -> P -> Q. *)
  | [ H: ~(?P /\ ?Q) |- _ ] => apply not_and_or_strong in H
  | [ |- ~(?P /\ ?Q) ] => apply or_not_and
  | [ H: ~(?P \/ ?Q) |- _ ] => apply not_or_and in H
  | [ |- ~(?P \/ ?Q) ] => apply and_not_or
  | [ H: ~(forall n, ~?P n) |- _ ] => apply not_all_not_ex in H
  | [ H: ~(forall n, ?P) |- _ ] => apply not_all_ex_not in H; destruct H as [n H]
  | [ H: ~(exists n, ?P) |- _ ] => apply Coqlib.not_ex_all_not in H; unfold NW in H
  | [ H: ~(exists n, ~?P n) |- _ ] => apply not_ex_not_all in H
  | [ |- ~(forall n, ?P n) ] => apply ex_not_not_all
  | [ |- ~(exists n, ?P n) ] => apply all_not_not_ex
  end
.

Ltac Psimpl := repeat Psimpl_.

Goal (~ forall (mm: nat), mm = 0%nat) -> exists n, n <> 0%nat.
  ii. Psimpl. exists mm. assumption.
Qed.

Goal (~ exists (mm: nat), mm = 0%nat) -> forall mm, mm <> 0%nat.
  intro H. Psimpl. assumption.
Qed.

Lemma iff_eta
      (P Q: Prop)
      (EQ: P = Q)
  :
    <<EQ: P <-> Q>>
.
Proof. clarify. Qed.

Lemma and_eta
      (P0 P1 Q0 Q1: Prop)
      (EQ0: P0 = P1)
      (EQ1: Q0 = Q1)
  :
    <<EQ: (P0 /\ Q0) = (P1 /\ Q1)>>
.
Proof. clarify. Qed.

Ltac smart_intro T :=
  intro;
  let x := match goal with
           | [ H: _ |- _ ] => H
           end
  in
  (* idtac x; *)
  on_last_hyp ltac:(fun id => revert id);

  let name := fresh "H" in
  intro name;
  let y := match goal with
           | [ H: _ |- _ ] => H
           end
  in
  (* idtac y; *)
  on_last_hyp ltac:(fun id => revert id);

  tryif (check_equal x y)
  then
    let name := fresh T in intro name
    (* (tryif check_hyp T *)
    (*   then (tryif check_hyp "U" *)
    (*          then (tryif (check_hyp "V") *)
    (*                 then (let name := (fresh "W") in intro name) *)
    (*                 else (let name := (fresh "V") in intro name)) *)
    (*          else (let name := (fresh "U") in intro name)) *)
    (*   else (let name := (fresh "T") in intro name)) *)

    (* (tryif check_hyp string:("T") *)
    (*   then (tryif check_hyp string:("U") *)
    (*          then (tryif (check_hyp string:("V")) *)
    (*                 then (intro W) *)
    (*                 else (intro V)) *)
    (*          else (intro U)) *)
    (*   else (intro T)) *)

    (* let T := fresh "T" in *)
    (* let U := fresh "U" in *)
    (* let V := fresh "V" in *)
    (* let W := fresh "W" in *)
    (* (tryif check_hyp T *)
    (*   then (tryif check_hyp U *)
    (*          then (tryif (check_hyp V) *)
    (*                 then (intro W) *)
    (*                 else (intro V)) *)
    (*          else (intro U)) *)
    (*   else (intro T)) *)
  else intro x

  (* match x with *)
  (* | y => let name := fresh T in *)
  (*        intro name *)
  (* | _ => intro x *)
  (* end *)
.

Tactic Notation "ii" "as" ident(a) := repeat (let name := fresh a in intro name).
(* Ltac sii := repeat (smart_intro "X"). *)
Tactic Notation "sii" ident(X) := repeat (smart_intro X).
Goal forall (t: True), True -> forall (u: True), True -> False.
Proof.
  sii T.
  clear t. clear T. clear u. clear T0.
Abort.

Require Import String.
Module Type SEAL.
  Parameter sealing: string -> forall X: Type, X -> X.
  Parameter sealing_eq: forall key X (x: X), sealing key x = x.
End SEAL.
Module Seal: SEAL.
  Definition sealing (_: string) X (x: X) := x.
  Lemma sealing_eq key X (x: X): sealing key x = x.
  Proof. refl. Qed.
End Seal.

Ltac seal_with key x :=
  replace x with (Seal.sealing key x); [|eapply Seal.sealing_eq].
Ltac seal x :=
  let key := fresh "key" in
  assert (key:= "_deafult_");
  seal_with key x.
Ltac unseal x :=
  match (type of x) with
  | string => repeat rewrite (@Seal.sealing_eq x) in *; try clear x
  | _ => repeat rewrite (@Seal.sealing_eq _ _ x) in *;
         repeat match goal with
                | [ H: string |- _ ] => try clear H
                end
  end
.

Notation "☃ y" := (Seal.sealing _ y) (at level 60, only printing).
Goal forall x, 5 + 5 = x. i. seal 5. seal x. Fail progress cbn. unseal key0. unseal 5. progress cbn. Abort.
Goal forall x y z, x + y = z. i. seal x. seal y. unseal y. unseal key. Abort.
Goal forall x y z, x + y = z. i. seal_with "a" x. seal_with "b" y. unseal "a". unseal "b". Abort.


Definition  shelve__ (A: Type) := A.

Ltac unshelve_goal :=
  match goal with
  | [|- shelve__ _] => shelve
  | _ => idtac
  end.

Notation "f ∘ g" := (fun x => (f (g x))).





Definition map_fst A B C (f: A -> C): A * B -> C * B := fun '(a, b) => (f a, b).
Definition map_snd A B C (f: B -> C): A * B -> A * C := fun '(a, b) => (a, f b).



(* Definition is_zero (v: Z): bool := (dec v 0%Z)%Z. *)

Ltac on_first_hyp tac :=
  match reverse goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

Ltac idtacs Hs :=
  match Hs with
  | (?H0, ?H1) => idtacs H0; idtacs H1
  | ?H => idtac H
  end
.

Notation "(∘)" := (fun g f => g ∘ f) (at level 0, left associativity).

Variant option_rel A B (P: A -> B -> Prop): option A -> option B -> Prop :=
| option_rel_some
    a b (IN: P a b)
  :
    option_rel P (Some a) (Some b)
| option_rel_none
  :
    option_rel P None None
.
Hint Constructors option_rel: core.

Definition map_or_else X Y (ox: option X) (f: X -> Y) (d: Y) :=
  match ox with | Some x => f x | None => d end.

Lemma map_or_else_same: forall X Y (ox: option X) (d: Y), map_or_else ox (fun _ => d) d = d.
  i. destruct ox; ss.
Qed.

Definition or_else X (ox: option X) (d: X) := match ox with | Some x => x | None => d end.

Lemma map_or_else_id: forall X ox (d: X), map_or_else ox id d = or_else ox d. refl. Qed.

Lemma flat_map_map A B C (f: A -> B) (g: B -> list C) (l: list A)
  :
    flat_map g (map f l) = flat_map (g ∘ f) l.
Proof.
  induction l; ss. f_equal; auto.
Qed.

Lemma fold_right_app_flat_map A B (f: A -> list B) l
  :
    flat_map f l
    =
    fold_right (@app _) [] (List.map f l).
Proof.
  induction l; ss. f_equal. auto.
Qed.

Lemma map_flat_map A B C (f: A -> list B) (g: B -> C) (l: list A)
  :
    List.map g (flat_map f l)
    =
    flat_map (List.map g) (List.map f l).
Proof.
  induction l; ss. rewrite List.map_app. f_equal; auto.
Qed.

Lemma flat_map_single A B (f: A -> B) (l: list A)
  :
    flat_map (fun a => [f a]) l
    =
    List.map f l.
Proof.
  induction l; ss.
Qed.

Lemma Forall2_In_l A B R (l0: list A) (l1: list B) a
      (FORALL2: Forall2 R l0 l1)
      (IN: In a l0)
  :
    exists b, In b l1 /\ R a b.
Proof.
  revert IN. induction FORALL2; ss. i. des.
  { subst. et. }
  { eapply IHFORALL2 in IN; et. i. des. esplits; et. }
Qed.

Lemma Forall2_In_r A B R (l0: list A) (l1: list B) b
      (FORALL2: Forall2 R l0 l1)
      (IN: In b l1)
  :
    exists a, In a l0 /\ R a b.
Proof.
  revert IN. induction FORALL2; ss. i. des.
  { subst. et. }
  { eapply IHFORALL2 in IN; et. i. des. esplits; et. }
Qed.

Lemma Forall2_eq
      A
      (xs0 xs1: list A)
      (EQ: Forall2 eq xs0 xs1)
  :
    <<EQ: xs0 = xs1>>
.
Proof. induction EQ; ss. des; subst. refl. Qed.

Global Open Scope nat_scope.
