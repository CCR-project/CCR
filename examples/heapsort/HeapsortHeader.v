Require Import Coq.Lists.List.
Import Nat.
Import ListNotations.

Definition option_bind {A B : Type} : option A -> (A -> option B) -> option B :=
  fun m k =>
    match m with
    | None => None
    | Some x => k x
    end.

Section Swap.

  Context {A B : Type}.

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

End Swap.

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
