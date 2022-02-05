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

Section Utilities.

  Definition option2list {A : Type} : option A -> list A :=
    @option_rect A (fun _ => list A) (fun x => [x]) [].

  Definition pair2list {A : Type} : A * A -> list A :=
    fun '(x1, x2) => [x1; x2].

  Lemma Some_inj {A : Type} {lhs : A} {rhs : A} :
    Some lhs = Some rhs -> lhs = rhs.
  Proof. congruence. Qed.

  Theorem divmod_inv a b q r (H_b_ne_0 : b <> 0) :
    (a = b * q + r /\ r < b)%nat <->
    (q = (a - r) / b /\ r = a mod b /\ a >= r)%nat.
  Proof with lia || eauto.
    assert (lemma1 := Nat.div_mod).
    enough (lemma2 : forall x : nat, forall y : nat, x > y <-> (exists z : nat, x = S (y + z))). split.
    - intros [H_a H_r_bound].
      assert (claim1 : a = b * (a / b) + (a mod b))...
      assert (claim2 : 0 <= a mod b /\ a mod b < b). apply (Nat.mod_bound_pos a b)...
      assert (claim3 : a >= r)...
      enough (claim4 : ~ q > a / b). enough (claim5 : ~ q < a / b). enough (claim6 : q = a / b)...
      + split... replace (a - r) with (q * b)... symmetry; apply Nat.div_mul...
      + intros H_false. destruct (proj1 (lemma2 (a / b) q) H_false) as [x Hx]...
      + intros H_false. destruct (proj1 (lemma2 q (a / b)) H_false) as [x Hx]...
    - intros [H_q [H_r H_a_ge_r]].
      assert (claim1 := Nat.mod_bound_pos a b). split...
      assert (claim2 : r < b)... assert (claim3 := Nat.div_mod a b H_b_ne_0).
      rewrite <- H_r in claim3. enough (claim4 : q = a / b)...
      rewrite H_q; symmetry. apply Nat.div_unique with (r := 0)...
    - intros x y; split.
      + intros Hgt; induction Hgt as [ | m Hgt [z Hz]]; [exists (0) | rewrite Hz]...
      + intros [z Hz]...
  Qed.

  Lemma positive_odd n_odd n :
    (n_odd = 2 * n + 1)%nat <->
    (n = (n_odd - 1) / 2 /\ n_odd mod 2 = 1 /\ n_odd > 0)%nat.
  Proof with lia || eauto.
    assert (claim1 := divmod_inv n_odd 2 n 1)...
  Qed.

  Lemma positive_even n_even n :
    (n_even = 2 * n + 2)%nat <->
    (n = (n_even - 2) / 2 /\ n_even mod 2 = 0 /\ n_even > 0)%nat.
  Proof with lia || eauto.
    assert (claim1 := divmod_inv (n_even - 2) 2 n 0). split.
    - intros ?; subst.
      assert (claim2 : n = (2 * n + 2 - 2 - 0) / 2 /\ 0 = (2 * n + 2 - 2) mod 2 /\ 2 * n + 2 - 2 >= 0)...
      split. rewrite (proj1 claim2) at 1. replace (2 * n + 2 - 2 - 0) with (2 * n + 2 - 2)...
      split... replace (2 * n + 2) with (2 + n * 2)... rewrite Nat.mod_add...
    - intros [H_n [H_r H_gt_0]].
      assert (claim2 : n_even >= 2). destruct n_even as [ | [ | n_even]]... inversion H_r.
      assert (claim3 : n_even = 2 * (n_even / 2) + n_even mod 2). apply Nat.div_mod...
      enough (claim4 : (n_even - 2) mod 2 = 0).
      + assert (claim5 : n_even - 2 = 2 * n + 0 /\ 0 < 2)...
        rewrite H_r, Nat.add_0_r in claim3. apply claim1...
        replace (n_even - 2 - 0) with (n_even - 2)...
      + transitivity (n_even mod 2)...
        symmetry; replace (n_even) with ((n_even - 2) + 1 * 2) at 1... apply Nat.mod_add...
  Qed.

  Lemma fold_left_last {A B : Type} (f : B -> A -> B) (z0 : B) (xs : list A) (x0 : A) :
    fold_left f (xs ++ [x0]) z0 = f (fold_left f xs z0) x0.
  Proof. revert z0 x0; induction xs as [ | x xs IH]; simpl; eauto. Qed.

  Lemma rev_inj {A : Type} (xs1 xs2 : list A)
    (H_rev_eq : rev xs1 = rev xs2)
    : xs1 = xs2.
  Proof.
    rewrite <- rev_involutive with (l := xs1).
    rewrite <- rev_involutive with (l := xs2).
    now apply f_equal.
  Qed.

End Utilities.

Section ListOperations.

  Context {A : Type}.

  Definition lookup (xs : list A) i := nth_error xs i.
  Definition lookup_1 (xs : list A) i := lookup xs (i-1).

  Definition swap_aux (xs : list A) i1 i2 x i :=
    if Nat.eq_dec i i1 then nth i2 xs x else
    if Nat.eq_dec i i2 then nth i1 xs x else
    x.
  Definition add_indices (xs : list A) := (combine xs (seq 0 (length xs))).
  Definition swap (xs : list A) i j := map (uncurry (swap_aux xs i j)) (add_indices xs).
  Definition swap_1 (xs : list A) i j := swap xs (i-1) (j-1).

End ListOperations.

Inductive bintree (A : Type) : Type :=
| BT_nil
| BT_node (x : A) (l r : bintree A)
.

Arguments BT_nil {A}.
Arguments BT_node {A} x l r.

Section CompleteBinaryTree.

  Context {A : Type}.

  Inductive is_perfect : bintree A -> nat -> Prop :=
  | perfect_nil : is_perfect BT_nil O
  | perfect_node {n : nat} x l r
                 (H_l : is_perfect l n)
                 (H_r : is_perfect r n)
    : is_perfect (BT_node x l r) (S n)
  .

  Inductive is_complete : bintree A -> nat -> Prop :=
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

  Lemma perfect2complete {n} t
    (H_perfect : is_perfect t n)
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

  Fixpoint get_rank (t : bintree A) : nat :=
    match t with
    | BT_nil => 0
    | BT_node x l r => 1 + max (get_rank l) (get_rank r)
    end.

  Lemma is_perfect_rank t rank
    (H_perfect : is_perfect t rank)
    : get_rank t = rank.
  Proof. induction H_perfect; simpl; lia. Qed.

  Lemma is_complete_rank t rank
    (H_complete : is_complete t rank)
    : get_rank t = rank.
  Proof. induction H_complete. 2: apply is_perfect_rank in H_l. all: simpl; lia. Qed.

  Definition fromList : list A -> bintree A.
  Admitted.

  Let cnt : bintree A -> nat :=
    fix cnt_fix t :=
    match t with
    | BT_nil => 1
    | BT_node x l r => 1 + cnt_fix l + cnt_fix r
    end.

  Program Fixpoint toList_step ts {measure (list_sum (map cnt ts))} : list A :=
    match ts with
    | [] => []
    | BT_nil :: ts_tail => toList_step ts_tail
    | BT_node x l r :: ts_tail => x :: toList_step ((ts_tail ++ [l]) ++ [r])
    end.
  Next Obligation.
    unfold Peano.lt.
    do 2 rewrite map_last. do 2 rewrite list_sum_app; cbn.
    do 2 rewrite Nat.add_0_r. rewrite <- Nat.add_assoc at 1.
    rewrite Nat.add_comm; constructor.
  Defined.

  Lemma toList_step_unfold ts :
    toList_step ts =
    match ts with
    | [] => []
    | BT_nil :: ts_tail => toList_step ts_tail
    | BT_node x l r :: ts_tail => x :: toList_step (ts_tail ++ [l; r])
    end.
  Proof with eauto.
    unfold toList_step at 1; rewrite fix_sub_eq.
    - destruct ts as [ | [ | x l r] ts_tail]...
      simpl; apply f_equal.
      replace ((ts_tail ++ [l]) ++ [r]) with (ts_tail ++ [l; r]) at 1...
      rewrite <- app_assoc...
    - intros [ | [ | x l r] ts_tail] ? ? ?...
      apply f_equal...
  Qed.

  Global Opaque toList_step.

  Definition option_root (t : bintree A) :=
    match t with
    | BT_nil => None
    | BT_node x l r => Some x
    end.

  Definition option_children_pair (t : bintree A) :=
    match t with
    | BT_nil => None
    | BT_node x l r => Some (l, r)
    end.

  Local Open Scope program_scope.

  Definition extract_elements := flat_map (option2list ∘ option_root).

  Definition extract_children := flat_map (@concat (bintree A) ∘ option2list ∘ option_map pair2list ∘ option_children_pair).

  Lemma extract_elements_unfold ts :
    extract_elements ts =
    match ts with
    | [] => []
    | BT_nil :: ts_tail => extract_elements ts_tail
    | BT_node x l r :: ts_tail => x :: extract_elements ts_tail
    end.
  Proof. destruct ts as [ | [ | x l r] ts_tail]; reflexivity. Qed.

  Lemma extract_children_unfold ts :
    extract_children ts =
    match ts with
    | [] => []
    | BT_nil :: ts_tail => extract_children ts_tail
    | BT_node x l r :: ts_tail => [l; r] ++ extract_children ts_tail
    end.
  Proof. destruct ts as [ | [ | x l r] ts_tail]; reflexivity. Qed.

  Lemma toList_step_app prevs nexts :
    toList_step (prevs ++ nexts) =
    extract_elements prevs ++ toList_step (nexts ++ extract_children prevs).
  Proof with eauto with *.
    revert nexts; induction prevs as [ | [ | x l r] prevs IH]; simpl.
    all: intros nexts; autorewrite with list...
    { rewrite toList_step_unfold... }
    { rewrite toList_step_unfold, <- app_assoc, IH, <- app_assoc... }
  Qed.

  Theorem toList_step_spec ts :
    toList_step ts =
    extract_elements ts ++ toList_step (extract_children ts).
  Proof. replace (ts) with (ts ++ []) at 1; [exact (toList_step_app ts []) | apply app_nil_r]. Qed.

  Definition toList root := toList_step [root].

  Lemma toList_fromList xs : toList (fromList xs) = xs.
  Admitted.

End CompleteBinaryTree.

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

Section HeapProperty.

  Context {A : Type}.
  Variable R : A -> A -> Prop.

  Inductive heap : bintree A -> Prop :=
  | heap_nil
    : heap (BT_nil)
  | heap_node x l r
    (R_x_l : @option_rect A (fun _ => Prop) (R x) (True) (option_root l))
    (R_x_r : @option_rect A (fun _ => Prop) (R x) (True) (option_root r))
    (heap_l : heap l)
    (heap_r : heap r)
    : heap (BT_node x l r).

End HeapProperty.

Section BinaryTreeAccessories.

  Inductive dir_t : Set := Dir_left | Dir_right.

  Fixpoint option_subtree {A : Type} ds t : option (bintree A) :=
    match ds with
    | [] => Some t
    | d :: ds' =>
      match t with
      | BT_nil => None
      | BT_node x l r => option_subtree ds' (dir_t_rect (fun _ => bintree A) l r d)
      end
    end.

  Definition encode ds := fold_left (fun code : nat => dir_t_rect (fun _ => nat) (2 * code + 1) (2 * code + 2)) ds 0.

  Lemma encode_inj ds1 ds2
    (H_encode_eq : encode ds1 = encode ds2)
    : ds1 = ds2.
  Proof with lia || eauto.
    revert H_encode_eq. unfold encode; do 2 rewrite <- fold_left_rev_right.
    intros H_eq; apply rev_inj; revert H_eq.
    generalize (rev ds2) as xs2. generalize (rev ds1) as xs1. clear ds1 ds2.
    set (myF := fold_right (fun y x => dir_t_rect (fun _ : dir_t => nat) (2 * x + 1) (2 * x + 2) y) 0).
    induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl...
    - destruct x2; simpl dir_t_rect...
    - destruct x1; simpl dir_t_rect...
    - destruct x1; destruct x2; simpl dir_t_rect...
      all: intros H_eq; assert (claim1 : myF xs1 = myF xs2)...
      all: apply f_equal...
  Qed.

  Lemma decodable code :
    {ds : list dir_t | encode ds = code}.
  Proof with lia || eauto.
    induction code as [[ | n'] IH] using Wf_nat.lt_wf_rect1.
    - exists ([])...
    - set (code := S n').
      destruct (code mod 2) as [ | [ | code_mod_2]] eqn: H_obs.
      + assert (claim1 : code = 2 * ((code - 2) / 2) + 2).
        { apply (positive_even code ((code - 2) / 2))... }
        assert (claim2 : (code - 2) / 2 < code)...
        destruct (IH ((code - 2) / 2) claim2) as [ds H_ds].
        exists (ds ++ [Dir_right]).
        unfold encode. rewrite fold_left_last. unfold dir_t_rect at 1.
        unfold encode in H_ds. rewrite H_ds...
      + assert (claim1 : code = 2 * ((code - 1) / 2) + 1).
        { apply (positive_odd code ((code - 1) / 2))... }
        assert (claim2 : (code - 1) / 2 < code)...
        destruct (IH ((code - 1) / 2) claim2) as [ds H_ds].
        exists (ds ++ [Dir_left]).
        unfold encode. rewrite fold_left_last. unfold dir_t_rect at 1.
        unfold encode in H_ds. rewrite H_ds...
      + pose (Nat.mod_bound_pos code 2)...
  Defined.

(*
  Compute (proj1_sig (decodable 14)).
  (* = [Dir_right; Dir_right; Dir_right] *)
  Compute (proj1_sig (decodable 15)).
  (* = [Dir_left; Dir_left; Dir_left; Dir_left] *)
  Compute (proj1_sig (decodable 16)).
  (* = [Dir_left; Dir_left; Dir_left; Dir_right] *)
*)

  Definition decode (code : nat) : list dir_t :=
    proj1_sig (decodable code).

  Global Opaque decode.

  Lemma encode_decode code :
    encode (decode code) = code.
  Proof. exact (proj2_sig (decodable code)). Qed.

  Definition subtree {A : Type} : nat -> bintree A -> bintree A.
  Admitted.

  Definition ctx_t A := list (dir_t * (A * bintree A)).

  Definition zipper A : Type := ctx_t A * bintree A.

  Context {A : Type}.

  Definition initZipper (root : bintree A) : zipper A := ([], root).

  Inductive ctx_spec s : ctx_t A -> bintree A -> Prop :=
  | CtxSpec_top
    : ctx_spec s [] s
  | CtxSpec_left c_l x l r
    (X_l : ctx_spec s c_l l)
    : ctx_spec s (c_l ++ [(Dir_left, (x, r))]) (BT_node x l r)
  | CtxSpec_right c_r x l r
    (X_r : ctx_spec s c_r r)
    : ctx_spec s (c_r ++ [(Dir_right, (x, l))]) (BT_node x l r).

  Local Hint Constructors ctx_spec : core.

  Lemma ctx_spec_refl root
    : ctx_spec root [] root.
  Proof. constructor. Qed.

  Lemma ctx_spec_trans t1 c1 t2 c2 root
    (X1 : ctx_spec t1 c1 t2)
    (X2 : ctx_spec t2 c2 root)
    : ctx_spec t1 (c1 ++ c2) root.
  Proof with eauto with *.
    revert t2 c2 X2 t1 c1 X1; intros t2 c2 X2.
    induction X2; intros t1 c1 X1; [rewrite app_nil_r | rewrite app_assoc | rewrite app_assoc]...
  Qed.

  Definition runZipper_step it : bintree A -> bintree A :=
    match fst it with
    | Dir_left => fun l => uncurry (fun x r => BT_node x l r) (snd it)
    | Dir_right => fun r => uncurry (fun x l => BT_node x l r) (snd it)
    end.

  Definition runZipper : zipper A -> bintree A :=
    fun '(c, s) => fold_right runZipper_step s (rev c).

  Lemma runZipper_unfold c s :
    runZipper (c, s) =
    match c with
    | [] => s
    | (Dir_left, (x, r)) :: c_l => runZipper (c_l, BT_node x s r)
    | (Dir_right, (x, l)) :: c_r => runZipper (c_r, BT_node x l s)
    end.
  Proof with eauto.
    cbn. rewrite fold_left_rev_right with (f := runZipper_step).
    destruct c as [ | [[ | ] [x t]] c]; simpl...
    all: rewrite fold_left_rev_right with (f := runZipper_step)...
  Qed.

  Lemma runZipper_last c d x t s :
    runZipper (c ++ [(d, (x, t))], s) =
    match d with
    | Dir_left => BT_node x (runZipper (c, s)) t
    | Dir_right => BT_node x t (runZipper (c, s))
    end.
  Proof. cbn. now rewrite rev_unit; destruct d. Qed.

  Definition zipper_invariant root : zipper A -> Prop :=
    fun '(c, s) => ctx_spec s c root.

  Theorem runZipper_spec root c s :
    root = runZipper (c, s) <->
    zipper_invariant root (c, s).
  Proof with eauto.
    unfold zipper_invariant; split.
    - intros H_eq; subst root; revert s.
      induction c as [ | [[ | ] [x t]] c IH] using rev_ind...
      all: intros s; rewrite runZipper_last...
    - intros X; induction X...
      all: rewrite runZipper_last, IHX...
  Qed.

  Corollary zipper_invariant_top root s :
    zipper_invariant root ([], s) <->
    root = s.
  Proof. now rewrite <- runZipper_spec. Qed.

  Corollary zipper_invariant_left root c x l r :
    zipper_invariant root ((Dir_left, (x, r)) :: c, l) <->
    zipper_invariant root (c, BT_node x l r).
  Proof. do 2 rewrite <- runZipper_spec. now rewrite runZipper_unfold at 1. Qed.

  Corollary zipper_invariant_right root c x l r :
    zipper_invariant root ((Dir_right, (x, l)) :: c, r) <->
    zipper_invariant root (c, BT_node x l r).
  Proof. do 2 rewrite <- runZipper_spec. now rewrite runZipper_unfold at 1. Qed.

  Local Hint Resolve zipper_invariant_top zipper_invariant_left zipper_invariant_right : core.

  Theorem zipper_invariant_unfold root c s :
    zipper_invariant root (c, s) <->
    match c with
    | [] => root = s
    | (Dir_left, (x, r)) :: c_l => zipper_invariant root (c_l, BT_node x s r)
    | (Dir_right, (x, l)) :: c_r => zipper_invariant root (c_r, BT_node x l s)
    end.
  Proof. destruct c as [ | [[ | ] [? ?]] ?]; eauto. Qed.

End BinaryTreeAccessories.

Section ListAccessories.

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
      { subst i. symmetry; apply nth_error_nth'... } 
      destruct (Nat.eq_dec i i2) as [H_yes2 | H_no2].
      { subst i. symmetry; apply nth_error_nth'... }
      symmetry...
    - exact (proj1 claim2).
  Qed.

End ListAccessories.
