Require Import
  List
  Setoid
  Compare_dec
  Morphisms
  FinFun
  PeanoNat
  Permutation
  Lia.
From Coq.Program Require Import Basics Wf.
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

Definition option2list {A : Type} : option A -> list A :=
  option_match [] (fun x => [x]).

Definition pair2list {A : Type} : A * A -> list A :=
  fun '(x1, x2) => [x1; x2].

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

(*
  Inductive perfect_bintree : nat -> Type :=
  | perfect_nil : perfect_bintree O
  | perfect_node {n : nat}
                 (x : A) (l : perfect_bintree n) (r : perfect_bintree n)
    : perfect_bintree (S n)
  .
*)

  Inductive is_perfect : bintree -> forall rank : nat, Prop :=
  | perfect_nil : is_perfect BT_nil O
  | perfect_node {n : nat} x l r
                 (H_l : is_perfect l n)
                 (H_r : is_perfect r n)
    : is_perfect (BT_node x l r) (S n)
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

  Inductive is_complete : bintree -> forall rank : nat, Prop :=
  | complete_nil
    : is_complete BT_nil O
  | complete_node_perfect_complete {n : nat} x l r
                                   (H_l : is_perfect l n)
                                   (H_r : is_complete r n)
    : is_complete (BT_node x l r) (S n)
  | complete_node_complete_perfect {n : nat} x l r
                                   (H_l : is_complete l (S n))
                                   (H_r : is_complete r n)
    : is_complete (BT_node x l r) (S (S n))
  .

(*
  Fixpoint perfect2complete {n} (t : perfect_bintree n) : complete_bintree n :=
    match t with
    | perfect_nil => complete_nil
    | perfect_node x l r => complete_node_perfect_complete x l (perfect2complete r)
    end.
*)

  Lemma perfect2complete {n} t (H_perfect : is_perfect t n)
    : is_complete t n.
  Proof.
    induction H_perfect as [ | n x l r H_l IH_l H_r IH_r].
    - exact (complete_nil).
    - exact (complete_node_perfect_complete x l r H_l IH_r).
  Qed.

(*
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

  Fixpoint get_rank t : nat :=
    match t with
    | BT_nil => 0
    | BT_node x l r => 1 + max (get_rank l) (get_rank r)
    end.

  Lemma is_perfect_rank t r :
    is_perfect t r ->
    get_rank t = r.
  Proof. intros X; induction X; simpl; lia. Qed.

  Lemma is_complete_rank t r :
    is_perfect t r ->
    get_rank t = r.
  Proof. intros X; induction X; simpl; lia. Qed.

(*
  Let cnt : bintree -> nat :=
    fix cnt_fix t :=
    match t with
    | BT_nil => 1
    | BT_node x l r => 1 + cnt_fix l + cnt_fix r
    end.

  Program Fixpoint toList_aux ts {measure (list_sum (map cnt ts))} :=
    match ts with
    | [] => []
    | BT_nil :: ts_tail => toList_aux ts_tail
    | BT_node x l r :: ts_tail => x :: toList_aux ((ts_tail ++ [l]) ++ [r])
    end.
  Next Obligation.
    unfold Peano.lt.
    do 2 rewrite map_last. do 2 rewrite list_sum_app; cbn.
    do 2 rewrite Nat.add_0_r. rewrite <- Nat.add_assoc at 1.
    rewrite Nat.add_comm; constructor.
  Defined.

  Lemma toList_aux_unfold ts :
    toList_aux ts =
    match ts with
    | [] => []
    | BT_nil :: ts_tail => toList_aux ts_tail
    | BT_node x l r :: ts_tail => x :: toList_aux (ts_tail ++ [l; r])
    end.
  Proof.
  Admitted.

  Global Opaque toList_aux.

  Definition toList root := toList_aux [root].
*)

  Inductive qtrav_spec : list bintree -> list A -> Prop :=
  | qtrav_spec1
    : qtrav_spec [] []
  | qtrav_spec2 ts xs
    (IH_spec : qtrav_spec ts xs)
    : qtrav_spec (BT_nil :: ts) xs
  | qtrav_spec3 x l r ts xs
    (IH_spec : qtrav_spec ((ts ++ [l]) ++ [r]) xs)
    : qtrav_spec (BT_node x l r :: ts) (x :: xs).

  Local Hint Constructors qtrav_spec : core.

  Definition qtrav :
    { qtrav_body : list bintree -> list A
    | forall ts rs, qtrav_spec ts rs <-> qtrav_body ts = rs
    }.
  Proof with eauto.
    set (cnt :=
      fix cnt_fix (t : bintree) {struct t} : nat :=
      match t with
      | BT_nil => 1
      | BT_node x l r => 1 + cnt_fix l + cnt_fix r
      end
    ).
    set (f := fun ts => list_sum (map cnt ts)).
    set (R := fun ts1 ts2 => f ts1 < f ts2).
    assert (R_wf : well_founded R).
    { apply Wf_nat.well_founded_lt_compat with (f := f)... }
    assert (R_wf_rect : forall phi : list bintree -> Type, (forall t1, (forall t2, R t2 t1 -> phi t2) -> phi t1) -> forall t, phi t).
    { intros phi acc_hyp t. induction (R_wf t)... }
    enough (to_show : forall ts, {xs : list A | forall rs, qtrav_spec ts rs <-> xs = rs}).
    { exists (fun ts => proj1_sig (to_show ts)). exact (fun ts => proj2_sig (to_show ts)). }
    induction ts as [[ | [ | x l r] ts] IH] using R_wf_rect.
    - exists ([]); intros rs; split; intros H_spec.
      + inversion H_spec; subst...
      + subst...
    - assert (IH_arg : R ts (BT_nil :: ts)).
      { unfold R, f. cbn; constructor. }
      destruct (IH ts IH_arg) as [xs H_xs].
      exists (xs); intros rs; split; intros H_spec.
      + inversion H_spec; subst. apply H_xs...
      + subst. constructor. apply H_xs...
    - assert (IH_arg : R ((ts ++ [l]) ++ [r]) (BT_node x l r :: ts)).
      { unfold R, f. cbn; unfold Peano.lt.
        do 2 rewrite map_last. do 2 rewrite list_sum_app; cbn.
        do 2 rewrite Nat.add_0_r. rewrite <- Nat.add_assoc at 1.
        rewrite Nat.add_comm; constructor.
      }
      destruct (IH ((ts ++ [l]) ++ [r]) IH_arg) as [xs H_xs].
      exists (x :: xs); intros rs; split; intros H_spec.
      + inversion H_spec; subst. apply f_equal, H_xs...
      + subst. constructor; apply H_xs...
  Defined.

  Lemma qtrav_unfold ts :
    proj1_sig qtrav ts =
    match ts with
    | [] => []
    | BT_nil :: ts_tail => proj1_sig qtrav ts_tail
    | BT_node x l r :: ts_tail => x :: proj1_sig qtrav ((ts_tail ++ [l]) ++ [r])
    end.
  Proof with eauto.
    destruct qtrav as [qtrav_body H_qtrav_body]; simpl.
    destruct ts as [ | [ | x l r] ts_tail]; simpl; apply H_qtrav_body...
    all: constructor; apply H_qtrav_body...
  Qed.

  Definition toList_aux := proj1_sig qtrav.

  Lemma toList_aux_unfold queue :
    toList_aux queue =
    match queue with
    | [] => []
    | BT_nil :: queue_tail => toList_aux queue_tail
    | BT_node x l r :: queue_tail => x :: toList_aux (queue_tail ++ [l; r])
    end.
  Proof.
    unfold toList_aux; rewrite qtrav_unfold with (ts := queue).
    destruct queue as [ | [ | x l r] queue_tail]; try reflexivity.
    now rewrite <- app_assoc at 1; replace ([l] ++ [r]) with ([l; r]).
  Qed.

  Global Opaque toList_aux.

  Definition option_root t :=
    match t with
    | BT_nil => None
    | BT_node x l r => Some x
    end.

  Definition option_childs t :=
    match t with
    | BT_nil => None
    | BT_node x l r => Some (l, r)
    end.

  Local Open Scope program_scope.

  Definition extract_roots := flat_map (option2list ∘ option_root).

  Lemma extract_roots_unfold ts :
    extract_roots ts =
    match ts with
    | [] => []
    | BT_nil :: ts_tail => extract_roots ts_tail
    | BT_node x l r :: ts_tail => x :: extract_roots ts_tail
    end.
  Proof. destruct ts as [ | [ | x l r] ts]; eauto. Qed.

  Definition extract_childs := flat_map (concat (A := _) ∘ option2list ∘ option_map pair2list ∘ option_childs).

  Lemma extract_childs_unfold ts :
    extract_childs ts =
    match ts with
    | [] => []
    | BT_nil :: ts_tail => extract_childs ts_tail
    | BT_node x l r :: ts_tail => [l; r] ++ extract_childs ts_tail
    end.
  Proof. destruct ts as [ | [ | x l r] ts]; eauto. Qed.

  Local Opaque extract_roots extract_childs.

  Lemma toList_aux_app ts1 ts2 :
    toList_aux (ts1 ++ ts2) = extract_roots ts1 ++ toList_aux (ts2 ++ extract_childs ts1).
  Proof with eauto with *.
    revert ts2; induction ts1 as [ | [ | x l r] ts2 IH]; simpl; intros ts1.
    - rewrite app_nil_r...
    - rewrite extract_roots_unfold, extract_childs_unfold, toList_aux_unfold...
    - rewrite extract_roots_unfold, extract_childs_unfold, toList_aux_unfold.
      simpl; apply f_equal; rewrite <- app_assoc.
      replace (ts1 ++ l :: r :: extract_childs ts2) with ((ts1 ++ [l; r]) ++ extract_childs ts2)...
      rewrite <- app_assoc...
  Qed.

  Theorem toList_aux_spec ts :
    toList_aux ts = extract_roots ts ++ toList_aux (extract_childs ts).
  Proof. replace ts with (ts ++ []) at 1. apply toList_aux_app. apply app_nil_r. Qed.

  Definition toList root := toList_aux [root].

End CompleteBinaryTree.

Arguments bintree: clear implicits.

(*
  Compute toList (BT_node 1 (BT_node 2 (BT_node 4 (BT_node 8 BT_nil BT_nil) (BT_node 9 BT_nil BT_nil)) (BT_node 5 (BT_node 10 BT_nil BT_nil) (BT_node 11 BT_nil BT_nil))) (BT_node 3 (BT_node 6 (BT_node 12 BT_nil BT_nil) (BT_node 13 BT_nil BT_nil)) (BT_node 7 (BT_node 14 BT_nil BT_nil) (BT_node 15 BT_nil BT_nil)))).
  = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]
  : list nat
*)

(*
  Compute toList (BT_node 1 (BT_node 2 (BT_node 4 (BT_node 8 BT_nil BT_nil) (BT_node 9 BT_nil BT_nil)) (BT_node 5 (BT_node 10 BT_nil BT_nil) (BT_node 11 BT_nil BT_nil))) (BT_node 3 (BT_node 6 (BT_node 12 BT_nil BT_nil) (BT_node 13 BT_nil BT_nil)) (BT_node 7 (BT_node 14 BT_nil BT_nil) BT_nil))).
  = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]
  : list nat
*)

Section BinaryTreeAccessories.

  Inductive dir_t : Set := Dir_left | Dir_right.

  Definition context (A : Type) := list (dir_t * (A * bintree A)).

  Definition zipper A : Type := bintree A * context A.

  Context {A : Type}.

  Definition init_zipper root : zipper A := (root, []).

  Inductive zipper_invariant subtree : context A -> bintree A -> Prop :=
  | Zipper_top
    : zipper_invariant subtree [] subtree
  | Zipper_left ctx_l x l r
    (X_l : zipper_invariant subtree ctx_l l)
    : zipper_invariant subtree (ctx_l ++ [(Dir_left, (x, r))]) (BT_node x l r)
  | Zipper_right ctx_r x l r
    (X_r : zipper_invariant subtree ctx_r r)
    : zipper_invariant subtree (ctx_r ++ [(Dir_right, (x, l))]) (BT_node x l r).

  Local Hint Constructors zipper_invariant : core.

  Lemma zipper_invariant_refl root
    : zipper_invariant root [] root.
  Proof. constructor. Qed.

  Lemma zipper_invariant_trans t1 c1 t2 c2 root
    (X1 : zipper_invariant t1 c1 t2)
    (X2 : zipper_invariant t2 c2 root)
    : zipper_invariant t1 (c1 ++ c2) root.
  Proof with eauto with *.
    revert t2 c2 X2 t1 c1 X1; intros t2 c2 X2.
    induction X2; intros t1 c1 X1; [rewrite app_nil_r | rewrite app_assoc | rewrite app_assoc]...
  Qed.

  Definition run_zipper_step_aux d x t : bintree A -> bintree A :=
    match d with
    | Dir_left => fun l => BT_node x l t
    | Dir_right => fun r => BT_node x t r
    end.

  Definition run_zipper_step it := uncurry (run_zipper_step_aux (fst it)) (snd it).

  Definition run_zipper : zipper A -> bintree A :=
    fun '(subtree, ctx) => fold_right run_zipper_step subtree (rev ctx).

  Lemma run_zipper_unfold subtree ctx :
    run_zipper (subtree, ctx) =
    match ctx with
    | [] => subtree
    | (Dir_left, (x, r)) :: ctx_l => run_zipper (BT_node x subtree r, ctx_l)
    | (Dir_right, (x, l)) :: ctx_r => run_zipper (BT_node x l subtree, ctx_r)
    end.
  Proof with eauto.
    cbn. rewrite fold_left_rev_right with (f := run_zipper_step).
    destruct ctx as [ | [[ | ] [e t]] ctx]; simpl...
    all: rewrite fold_left_rev_right with (f := run_zipper_step)...
  Qed.

  Lemma run_zipper_last subtree ctx d x t :
    run_zipper (subtree, ctx ++ [(d, (x, t))]) =
    match d with
    | Dir_left => BT_node x (run_zipper (subtree, ctx)) t
    | Dir_right => BT_node x t (run_zipper (subtree, ctx))
    end.
  Proof. cbn. now rewrite rev_unit; destruct d. Qed.

  Theorem zipper_invariant_iff subtree ctx root :
    zipper_invariant subtree ctx root <->
    run_zipper (subtree, ctx) = root.
  Proof with eauto.
    split.
    - intros X; induction X...
      all: rewrite run_zipper_last, <- IHX...
    - intros H_eq; subst root; revert subtree.
      induction ctx as [ | [[ | ] [x t]] ctx IH] using rev_ind...
      all: intros subtree; rewrite run_zipper_last...
  Qed.

  Corollary zipper_invariant_top subtree root :
    zipper_invariant subtree [] root <->
    subtree = root.
  Proof. now rewrite zipper_invariant_iff. Qed.

  Corollary zipper_invariant_left ctx x l r root :
    zipper_invariant l ((Dir_left, (x, r)) :: ctx) root <->
    zipper_invariant (BT_node x l r) ctx root.
  Proof. do 2 rewrite zipper_invariant_iff. now rewrite run_zipper_unfold at 1. Qed.

  Corollary zipper_invariant_right ctx x l r root :
    zipper_invariant r ((Dir_right, (x, l)) :: ctx) root <->
    zipper_invariant (BT_node x l r) ctx root.
  Proof. do 2 rewrite zipper_invariant_iff. now rewrite run_zipper_unfold at 1. Qed.

End BinaryTreeAccessories.

Section ListAccessories.

  Lemma Some_inj {A : Type} {lhs : A} {rhs : A} :
    Some lhs = Some rhs -> lhs = rhs.
  Proof. congruence. Qed.

  Lemma list_extensionality {A : Type} (xs1 : list A) (xs2 : list A) :
    xs1 = xs2 <-> (forall i, lookup xs1 i = lookup xs2 i).
  Proof with discriminate || eauto.
    revert xs1 xs2; cbn.
    induction xs1 as [ | x1 xs1 IH]; intros [ | x2 xs2]; simpl in *; split; intros H_eq...
    - pose (H_eq 0)...
    - pose (H_eq 0)...
    - rewrite H_eq...
    - assert (H_x1_eq_x2 : x1 = x2) by exact (Some_inj (H_eq 0)); subst.
      pose (proj2 (IH xs2) (fun i => H_eq (S i))); congruence.
  Qed.

  Lemma listExt_map {A : Type} {B : Type} (f : A -> B) (xs : list A) :
    forall i, lookup (map f xs) i = option_map f (lookup xs i).
  Proof. cbn; induction xs as [ | x xs IH]; intros [ | n']; simpl; (discriminate || eauto). Qed.

  Lemma listExt_seq (start : nat) (len : nat) :
    forall i,
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
    forall i,
    i < length xs ->
    i < n ->
    nth_error (firstn n xs) i = nth_error xs i.
  Proof with discriminate || (try lia) || eauto.
    revert xs; induction n as [ | n IH]; simpl...
    intros [ | x xs] i H_lt1 H_lt2; simpl in *...
    destruct i as [ | i']; simpl... apply IH...
  Qed.

  Lemma listExt_firstn {A : Type} (xs : list A) (n : nat) :
    forall i,
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
    forall i,
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
      + assert (H_i : i < length (combine (firstn len xs) (firstn len ys))).
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
      + enough (to_show : len <= i) by lia.
        apply nth_error_None in H_obs.
        rewrite combine_length in H_obs.
        do 2 (rewrite firstn_length_le in H_obs; [ | lia]); lia.
    - rewrite <- combine_firstn; apply firstn_all2; rewrite combine_length...
  Qed.

  Lemma listExt_add_indices {A : Type} (xs : list A) :
    forall i, 
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
    forall i,
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

End ListAccessories.
