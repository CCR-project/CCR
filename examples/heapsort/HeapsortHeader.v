Require Import
  List
  Setoid
  Compare_dec
  Morphisms
  FinFun
  PeanoNat
  Permutation
  Lia.
Import Nat.
Import ListNotations.

Definition option_bind {A B : Type} : option A -> (A -> option B) -> option B :=
  fun m k =>
    match m with
    | None => None
    | Some x => k x
    end.

Definition option_match {A B : Type} : B -> (A -> B) -> option A -> B :=
  fun z0 f m =>
    match m with
    | None => z0
    | Some x => f x
    end.

Section ListOperations.

  Context {A : Type}.

  Definition lookup (xs : list A) i := nth_error xs i.
  Definition lookup_1 (xs : list A) i := lookup xs (i-1).

(*
  Fixpoint trim_prefix (xs : list A) (i : nat) {struct i} : option (list A) :=
    match xs, i with
    | [], _ => None
    | x :: xs', O => Some nil
    | x :: xs', S i' => option_map (cons x) (trim_prefix xs' i')
    end.

  Fixpoint trim_mid (xs : list A) (i : nat) {struct i} : option A :=
    match xs, i with
    | [], _ => None
    | x :: xs', O => Some x
    | x :: xs', S i' => trim_mid xs' i'
    end.
    
  Fixpoint trim_postfix (xs : list A) (i : nat) {struct i} : option (list A) :=
    match xs, i with
    | [], _ => None
    | x :: xs', O => Some xs'
    | x :: xs', S i' => trim_postfix xs' i'
    end.

  Fixpoint trim (xs : list A) (i : nat) {struct i} : option (list A * A * list A) :=
    match xs, i with
    | [], _ => None
    | x :: xs', O => Some ([], x, xs')
    | x :: xs', S i' => option_map (fun '(ls, m, rs) => (x :: ls, m, rs)) (trim xs' i')
    end.

  Definition trim3 (xs : list A) (i j : nat) : option (list A * A * list A * A * list A) :=
    if i =? j then None else
    let i' := min i j in
    let j' := max i j in
    let k' := j' - i' - 1 in
    option_bind (trim xs i') (fun '(ls, x, mrs) =>
                                option_map (fun '(ms, y, rs) => (ls, x, ms, y, rs)) (trim mrs k')).

  Definition swap (xs : list A) (i j : nat) : list A :=
    match trim3 xs i j with
    | Some (xs, x, ys, y, zs) => xs ++ [y] ++ ys ++ [x] ++ zs
    | None => xs
    end.
*)

  Definition swap_aux (xs : list A) (i1 : nat) (i2 : nat) (x : A) (i : nat) : A :=
    if Nat.eq_dec i i1 then option_match x id (lookup xs i2) else
    if Nat.eq_dec i i2 then option_match x id (lookup xs i1) else
    x.
  Definition add_indices (xs : list A) := (combine xs (seq 0 (length xs))).
  Definition swap (xs : list A) i j := map (uncurry (swap_aux xs i j)) (add_indices xs).
  Definition swap_1 (xs : list A) i j := swap xs (i-1) (j-1).

End ListOperations.

Section CompleteBinaryTree.

  Context {A : Type}.
  
  Inductive perfect_bintree : nat -> Type :=
  | perfect_nil : perfect_bintree O
  | perfect_node {n : nat}
                 (x : A) (l : perfect_bintree n) (r : perfect_bintree n)
    : perfect_bintree (S n)
  .
  
  Inductive complete_bintree : nat -> Type :=
  | complete_nil
    : complete_bintree O
  | complete_node_perfect_complete {n : nat}
                                   (x : A) (l : perfect_bintree n) (r : complete_bintree n)
    : complete_bintree (S n)
  | complete_node_complete_perfect {n : nat}
                                   (x : A) (l : complete_bintree (S n)) (r : perfect_bintree n)
    : complete_bintree (S (S n))
  .

  Fixpoint perfect2complete {n} (t : perfect_bintree n) : complete_bintree n :=
    match t with
    | perfect_nil => complete_nil
    | perfect_node x l r => complete_node_perfect_complete x l (perfect2complete r)
    end.

  Ltac destruct_perfect t x l r :=
    match goal with
    | [ H : perfect_bintree ?n |- _ ] => 
      constr_eq H t;
      let n0 := fresh "n" in
      let n1 := fresh "n" in
      let Heq := fresh "Heq" in
      remember n as n0 eqn: Heq in t;
      destruct H as [|n1 x l r];
      inversion Heq;
      subst;
      clear Heq
    end.

  Ltac destruct_complete t x l r :=
    match goal with
    | [ H : complete_bintree ?n |- _ ] =>
      constr_eq H t;
      let n0 := fresh "n" in
      let n1 := fresh "n" in
      let Heq := fresh "Heq" in
      remember n as n0 eqn: Heq in t;
      destruct H as [| n1 x l r | n1 x l r];
      inversion Heq;
      subst;
      clear Heq
    end.
  
  Fixpoint delete_last_perfect {n} (t : perfect_bintree (S (S n))) : complete_bintree (S (S n)).
  Proof.
    destruct_perfect t x l r.
    destruct n.
    - assert (l' : complete_bintree 1)
        by exact (perfect2complete l).
      exact (complete_node_complete_perfect x l' perfect_nil).
    - assert (r' : complete_bintree (S (S n)))
        by exact (delete_last_perfect _ r).
      exact (complete_node_perfect_complete x l r').
  Defined.

  Fixpoint delete_last_complete {n} (t : complete_bintree (S n)) : complete_bintree (S n) + perfect_bintree n.
  Proof.
    destruct_complete t x l r.
    - destruct n.
      + right. econstructor.
      + left.
        assert (r' : complete_bintree (S n) + perfect_bintree n) by exact (delete_last_complete _ r).
        destruct r' as [r'|r'].
        * exact (complete_node_perfect_complete x l r').
        * exact (complete_node_complete_perfect x (perfect2complete l) r').
    - assert (l' : complete_bintree (S n1) + perfect_bintree n1) by exact (delete_last_complete _ l).
      destruct l' as [l'|l'].
      + left. exact (complete_node_complete_perfect x l' r).
      + right. exact (perfect_node x l' r).
  Defined.

End CompleteBinaryTree.

Arguments perfect_bintree : clear implicits.
Arguments complete_bintree : clear implicits.

Section SwapProperties.

  Lemma Some_inj {A : Type} {lhs : A} {rhs : A} :
    Some lhs = Some rhs -> lhs = rhs.
  Proof. congruence. Qed.

  Definition listEXT_view {A : Type} (xs : list A) : forall idx : nat, {ret : option A | idx < length xs -> ret <> None} :=
    fun idx : nat =>
    exist _ (nth_error xs idx) (proj2 (nth_error_Some xs idx))
  .

  Definition safe_lookup {A : Type} (xs : list A) : forall idx : nat, idx < length xs -> A :=
    fun idx : nat =>
    fun H_idx : idx < length xs =>
    match proj1_sig (listEXT_view xs idx) as Some_x return Some_x <> None -> A with
    | None => fun H_no => False_rect A (H_no Logic.eq_refl)
    | Some x => fun _ => x
    end (proj2_sig (listEXT_view xs idx) H_idx)
  .

  Definition listExt_view {A : Type} (xs : list A) : nat -> option A :=
    fun idx : nat =>
    proj1_sig (listEXT_view xs idx)
  .

  Lemma list_extensionality {A : Type} (xs1 : list A) (xs2 : list A) :
    xs1 = xs2 <->
    forall i : nat,
    listExt_view xs1 i = listExt_view xs2 i.
  Proof with discriminate || eauto.
    revert xs1 xs2; cbn.
    induction xs1 as [ | x1 xs1 IH]; intros [ | x2 xs2]; simpl in *; split; intros H_eq...
    - pose (H_eq 0)...
    - pose (H_eq 0)...
    - rewrite H_eq...
    - assert (H_x1_eq_x2 : x1 = x2) by exact (Some_inj (H_eq 0)); subst x2.
      pose (proj2 (IH xs2) (fun i => H_eq (S i))); congruence.
  Qed.

  Lemma listExt_map {A : Type} {B : Type} (f : A -> B) (xs : list A) :
    forall i : nat,
    listExt_view (map f xs) i = (option_map f) (listExt_view xs i).
  Proof with discriminate || eauto.
    cbn; induction xs as [ | x xs IH]; simpl.
    - intros [ | n']...
    - intros [ | n']; simpl...
  Qed.

  Lemma listExt_seq (start : nat) (len : nat) :
    forall i : nat,
    match listExt_view (seq start len) i with
    | None => i >= len
    | Some x => x = start + i
    end.
  Proof with discriminate || eauto.
    intros i; cbn.
    destruct (nth_error (seq start len) i) as [x | ] eqn: H_obs.
    - assert (i_lt_len : i < length (seq start len)).
      { apply nth_error_Some. rewrite H_obs... }
      rewrite (nth_error_nth' (seq start len) x i_lt_len) in H_obs.
      apply Some_inj in H_obs; rewrite <- H_obs.
      apply seq_nth; rewrite seq_length in i_lt_len...
    - rewrite <- (seq_length len start); apply nth_error_None...
  Qed.

  Lemma firstn_nth_error {A : Type} (n : nat) (xs : list A)  :
    forall i : nat,
    i < length xs ->
    i < n ->
    nth_error (firstn n xs) i = nth_error xs i.
  Proof with discriminate || (try lia) || eauto.
    revert xs; induction n as [ | n IH]; simpl...
    intros [ | x xs] i H_lt1 H_lt2; simpl in *...
    destruct i as [ | i']; simpl...
    apply IH...
  Qed.

  Lemma listExt_firstn {A : Type} (xs : list A) (n : nat) :
    forall i : nat,
    match listExt_view (firstn n xs) i with
    | None => i >= n \/ i >= length xs
    | Some x => i < n /\ listExt_view xs i = Some x
    end.
  Proof with discriminate || eauto.
    intros i; cbn.
    destruct (nth_error (firstn n xs) i) as [x | ] eqn: H_obs.
    - assert (i_lt_len : i < length (firstn n xs)).
      { apply nth_error_Some. rewrite H_obs... }
      pose (firstn_length n xs); split; [lia | ].
      assert (i_lt_length_xs : i < length xs) by lia.
      rewrite <- H_obs; symmetry.
      apply firstn_nth_error; lia.
    - assert (i_ge_len : i >= length (firstn n xs)).
      { apply nth_error_None... }
      rewrite (firstn_length n xs) in i_ge_len; lia.
  Qed.

  Lemma listExt_combine {A : Type} {B : Type} (xs : list A) (ys : list B) :
    forall i : nat,
    match listExt_view (combine xs ys) i with
    | None => i >= length xs \/ i >= length ys
    | Some (x, y) => listExt_view xs i = Some x /\ listExt_view ys i = Some y
    end.
  Proof with discriminate || eauto.
    set (len := min (length xs) (length ys)).
    replace (combine xs ys) with (combine (firstn len xs) (firstn len ys)).
    - assert (H_len : length (firstn len xs) = length (firstn len ys)).
      { do 2 (rewrite firstn_length_le; [ | lia]); lia. }
      intros i; cbn.
      destruct (nth_error (combine (firstn len xs) (firstn len ys)) i) as [[x y] | ] eqn: H_obs.
      { assert (H_i : i < length (combine (firstn len xs) (firstn len ys))).
        { apply nth_error_Some; rewrite H_obs... }
        assert (H1_i : i < length (firstn len xs)).
        { pose (combine_length (firstn len xs) (firstn len ys)); lia. }
        assert (H2_i : i < length (firstn len ys)).
        { pose (combine_length (firstn len xs) (firstn len ys)); lia. }
        assert (claim1 := listExt_firstn xs len i).
        assert (claim2 := listExt_firstn ys len i).
        cbn in claim1, claim2.
        rewrite (nth_error_nth' (firstn len xs) x H1_i) in claim1.
        rewrite (nth_error_nth' (firstn len ys) y H2_i) in claim2.
        rewrite (nth_error_nth' (combine (firstn len xs) (firstn len ys)) (x, y) H_i) in H_obs.
        apply Some_inj in H_obs; rewrite (combine_nth (firstn len xs) (firstn len ys) i x y H_len) in H_obs.
        assert (x_is : x = nth i (firstn len xs) x) by congruence.
        assert (y_is : y = nth i (firstn len ys) y) by congruence.
        rewrite x_is, y_is; now firstorder.
      }
      { enough (to_show : len <= i) by lia.
        apply nth_error_None in H_obs.
        rewrite combine_length in H_obs.
        do 2 (rewrite firstn_length_le in H_obs; [ | lia]); lia.
      }
    - rewrite <- combine_firstn; apply firstn_all2; rewrite combine_length...
  Qed.

  Lemma listExt_add_indices {A : Type} (xs : list A) :
    forall i : nat, 
    match listExt_view (add_indices xs) i with
    | None => i >= length xs /\ listExt_view xs i = None
    | Some (x, n) => i = n /\ listExt_view xs i = Some x
    end.
  Proof with discriminate || eauto.
    intros i; cbn; unfold add_indices.
    assert (claim1 := listExt_combine xs (seq 0 (length xs)) i).
    unfold listExt_view in claim1; cbn in claim1.
    destruct (nth_error (combine xs (seq 0 (length xs))) i) as [[x n] | ] eqn: H_obs.
    - destruct claim1 as [H_obs_xs H_obs_seq].
      split...
      assert (claim2 := listExt_seq 0 (length xs) i).
      unfold listExt_view in claim2; cbn in claim2.
      rewrite H_obs_seq in claim2...
    - rewrite seq_length in claim1.
      rewrite nth_error_None; lia.
  Qed.

  Lemma listExt_swap {A : Type} (xs : list A) (i1 : nat) (i2 : nat) :
    i1 < length xs ->
    i2 < length xs ->
    forall i : nat,
    match listExt_view (swap xs i1 i2) i with
    | None => i >= length xs
    | Some val =>
      Some val =
      if Nat.eq_dec i i1 then nth_error xs i2 else
      if Nat.eq_dec i i2 then nth_error xs i1 else
      nth_error xs i
    end.
  Proof with discriminate || eauto.
    intros H_i1 H_i2.
    assert (H_lookup_i1 := proj2 (nth_error_Some xs i1) H_i1).
    assert (H_lookup_i2 := proj2 (nth_error_Some xs i2) H_i2).
    intros i; cbn; unfold swap.
    assert (claim1 := listExt_map (uncurry (swap_aux xs i1 i2)) (add_indices xs) i).
    unfold listExt_view in claim1; cbn in claim1.
    rewrite claim1; unfold option_map.
    assert (claim2 := listExt_add_indices xs i).
    unfold listExt_view in claim2; cbn in claim2.
    destruct (nth_error (add_indices xs) i) as [[x n] | ] eqn: H_obs_add_indices.
    - simpl; unfold swap_aux, lookup.
      destruct claim2 as [H_EQ H_obs_xs]; subst n.
      destruct (Nat.eq_dec i i1) as [H_yes1 | H_no1].
      { subst i. destruct (nth_error xs i2) eqn: H_obs_i2... contradiction. } 
      destruct (Nat.eq_dec i i2) as [H_yes2 | H_no2].
      { subst i. destruct (nth_error xs i1) eqn: H_obs_i1... contradiction. }
      symmetry...
    - exact (proj1 claim2).
  Qed.

End SwapProperties.
