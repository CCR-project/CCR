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

  Inductive bintree : Type :=
  | BT_nil
  | BT_node (x : A) (l : bintree) (r : bintree)
  .

  Inductive is_perfect : bintree -> forall rank : nat, Prop :=
  | Perfect_nil : is_perfect BT_nil O
  | Perfect_node {n : nat}
                 (x : A) (l : bintree) (r : bintree)
                 (H_l : is_perfect l n)
                 (H_r : is_perfect r n)
    : is_perfect (BT_node x l r) (S n)
  .

(*
  Inductive perfect_bintree : nat -> Type :=
  | perfect_nil : perfect_bintree O
  | perfect_node {n : nat}
                 (x : A) (l : perfect_bintree n) (r : perfect_bintree n)
    : perfect_bintree (S n)
  .
*)

  Inductive is_complete : bintree -> forall rank : nat, Prop :=
  | Complete_nil
    : is_complete BT_nil O
  | Complete_node_perfect_complete {n : nat}
                                   (x : A) (l : bintree) (r : bintree)
                                   (H_l : is_perfect l n)
                                   (H_r : is_complete r n)
    : is_complete (BT_node x l r) (S n)
  | Complete_node_complete_perfect {n : nat}
                                   (x : A) (l : bintree) (r : bintree)
                                   (H_l : is_complete l (S n))
                                   (H_r : is_complete r n)
    : is_complete (BT_node x l r) (S (S n))
  .

(*
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
*)

(*
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
*)

End CompleteBinaryTree.

Arguments bintree: clear implicits.

Section BinaryTreeAccessories.

  Inductive dir_t : Set := Dir_left | Dir_right.

  Definition context (A : Type) := list (dir_t * (A * bintree A)).

  Context {A : Type}.

  Definition recover_step_aux d x t : bintree A -> bintree A :=
    match d with
    | Dir_left => fun t_l => BT_node x t_l t
    | Dir_right => fun t_r => BT_node x t t_r
    end.

  Definition recover_step it := uncurry (recover_step_aux (fst it)) (snd it).

  Definition recover subtree ctx := fold_right recover_step subtree (rev ctx).

  Lemma recover_unfold subtree ctx :
    recover subtree ctx =
    match ctx with
    | [] => subtree
    | (Dir_left, (x, t_r)) :: ctx_l => recover (BT_node x subtree t_r) ctx_l
    | (Dir_right, (x, t_l)) :: ctx_r => recover (BT_node x t_l subtree) ctx_r
    end.
  Proof with eauto.
    unfold recover at 1; rewrite fold_left_rev_right with (f := recover_step).
    destruct ctx as [ | [[ | ] [e t]] ctx]; simpl...
    all: unfold recover at 1; rewrite fold_left_rev_right with (f := recover_step)...
  Qed.

  Lemma recover_last subtree ctx d x t :
    recover subtree (ctx ++ [(d, (x, t))]) =
    match d with
    | Dir_left => BT_node x (recover subtree ctx) t 
    | Dir_right => BT_node x t (recover subtree ctx)
    end.
  Proof. unfold recover at 1; rewrite rev_unit; now destruct d. Qed.

  Inductive context_spec subtree : context A -> bintree A -> Prop :=
  | CtxSpec_top
    : context_spec subtree [] subtree
  | CtxSpec_left ctx_l x t_l t_r
    (H_l : context_spec subtree ctx_l t_l)
    : context_spec subtree (ctx_l ++ [(Dir_left, (x, t_r))]) (BT_node x t_l t_r)
  | CtxSpec_right ctx_r x t_l t_r
    (H_r : context_spec subtree ctx_r t_r)
    : context_spec subtree (ctx_r ++ [(Dir_right, (x, t_l))]) (BT_node x t_l t_r).

  Local Hint Constructors context_spec : core.

  Theorem context_spec_recover subtree ctx root :
    context_spec subtree ctx root <->
    recover subtree ctx = root.
  Proof with eauto.
    split.
    - intros X; induction X; simpl...
      all: rewrite recover_last, IHX...
    - intros H_eq; subst root; revert subtree.
      pattern ctx; revert ctx; apply rev_ind...
      intros [[ | ] [x t]] ctx IH subtree; rewrite recover_last...
  Qed.

  Corollary context_spec_left ctx x t_l t_r root :
    context_spec (BT_node x t_l t_r) ctx root <->
    context_spec t_l ((Dir_left, (x, t_r)) :: ctx) root.
  Proof.
    do 2 rewrite context_spec_recover.
    now rewrite recover_unfold with (ctx := (Dir_left, (x, t_r)) :: ctx).
  Qed.

  Corollary context_spec_right ctx x t_l t_r root :
    context_spec (BT_node x t_l t_r) ctx root <->
    context_spec t_r ((Dir_right, (x, t_l)) :: ctx) root.
  Proof.
    do 2 rewrite context_spec_recover.
    now rewrite recover_unfold with (ctx := (Dir_right, (x, t_l)) :: ctx).
  Qed.

  Lemma context_spec_refl root
    : context_spec root [] root.
  Proof. constructor 1. Qed.

  Lemma context_spec_trans t1 c1 t2 c2 root
    (X1 : context_spec t1 c1 t2)
    (X2 : context_spec t2 c2 root)
    : context_spec t1 (c1 ++ c2) root.
  Proof with eauto with *.
    revert t2 c2 X2 t1 c1 X1; intros t2 c2 X2.
    induction X2; intros t1 c1 X1; [rewrite app_nil_r | rewrite app_assoc | rewrite app_assoc]...
  Qed.

End BinaryTreeAccessories.

Section SwapProperties.

  Search Some Logic.eq.

  Lemma Some_inj {A : Type} {lhs : A} {rhs : A} :
    Some lhs = Some rhs -> lhs = rhs.
  Proof. congruence. Qed.

  Lemma list_extensionality {A : Type} (xs1 : list A) (xs2 : list A) :
    xs1 = xs2 <->
    forall i : nat,
    lookup xs1 i = lookup xs2 i.
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
    lookup (map f xs) i = (option_map f) (lookup xs i).
  Proof with discriminate || eauto.
    cbn; induction xs as [ | x xs IH]; simpl.
    - intros [ | n']...
    - intros [ | n']; simpl...
  Qed.

  Lemma listExt_seq (start : nat) (len : nat) :
    forall i : nat,
    match lookup (seq start len) i with
    | None => i >= len
    | Some x => x = start + i
    end.
  Proof with discriminate || eauto.
    unfold lookup; intros i.
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
    match lookup (firstn n xs) i with
    | None => i >= n \/ i >= length xs
    | Some x => i < n /\ lookup xs i = Some x
    end.
  Proof with discriminate || (try lia) || eauto.
    intros i; unfold lookup.
    destruct (nth_error (firstn n xs) i) as [x | ] eqn: H_obs.
    - assert (i_lt_len : i < length (firstn n xs)).
      { apply nth_error_Some. rewrite H_obs... }
      pose (firstn_length n xs); split...
      assert (i_lt_length_xs : i < length xs)...
      rewrite <- H_obs; symmetry.
      apply firstn_nth_error...
    - assert (i_ge_len : i >= length (firstn n xs)).
      { apply nth_error_None... }
      rewrite (firstn_length n xs) in i_ge_len...
  Qed.

  Lemma listExt_combine {A : Type} {B : Type} (xs : list A) (ys : list B) :
    forall i : nat,
    match lookup (combine xs ys) i with
    | None => i >= length xs \/ i >= length ys
    | Some (x, y) => lookup xs i = Some x /\ lookup ys i = Some y
    end.
  Proof with discriminate || eauto.
    unfold lookup.
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
        unfold lookup in claim1, claim2.
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
    match lookup (add_indices xs) i with
    | None => i >= length xs /\ lookup xs i = None
    | Some (x, n) => i = n /\ lookup xs i = Some x
    end.
  Proof with discriminate || eauto.
    intros i; unfold lookup, add_indices.
    assert (claim1 := listExt_combine xs (seq 0 (length xs)) i).
    unfold lookup in claim1; cbn in claim1.
    destruct (nth_error (combine xs (seq 0 (length xs))) i) as [[x n] | ] eqn: H_obs.
    - destruct claim1 as [H_obs_xs H_obs_seq]; split...
      assert (claim2 := listExt_seq 0 (length xs) i).
      unfold lookup in claim2; cbn in claim2.
      rewrite H_obs_seq in claim2...
    - rewrite seq_length in claim1.
      rewrite nth_error_None; lia.
  Qed.

  Theorem listExt_swap {A : Type} (xs : list A) (i1 : nat) (i2 : nat) :
    i1 < length xs ->
    i2 < length xs ->
    forall i : nat,
    match lookup (swap xs i1 i2) i with
    | None => i >= length xs
    | Some val =>
      Some val =
      if Nat.eq_dec i i1 then lookup xs i2 else
      if Nat.eq_dec i i2 then lookup xs i1 else
      lookup xs i
    end.
  Proof with discriminate || eauto.
    intros H_i1 H_i2; unfold lookup.
    assert (H_lookup_i1 := proj2 (nth_error_Some xs i1) H_i1).
    assert (H_lookup_i2 := proj2 (nth_error_Some xs i2) H_i2).
    intros i; cbn; unfold swap.
    assert (claim1 := listExt_map (uncurry (swap_aux xs i1 i2)) (add_indices xs) i).
    unfold lookup in claim1; cbn in claim1.
    rewrite claim1; unfold option_map.
    assert (claim2 := listExt_add_indices xs i).
    unfold lookup in claim2; cbn in claim2.
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
