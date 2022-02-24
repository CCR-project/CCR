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
Local Open Scope program_scope.

Section Utilities.
  (*
  Definition option2list {A : Type} : option A -> list A :=
    @option_rect A (fun _ => list A) (fun x => [x]) [].

  Definition pair2list {A : Type} : A * A -> list A :=
    fun '(x1, x2) => [x1; x2].
   *)

  Definition isSome {A : Type} : option A -> Prop := fun m => m <> None.

  Definition isNone {A : Type} : option A -> Prop := fun m => m = None.

  Lemma isSome_intro {A : Type} (Some_x : option A) (x : A) : Some_x = Some x -> isSome Some_x.
  Proof. congruence. Qed.

  Lemma Some_or_None {A : Type} : forall m : option A,  {isSome m} + {isNone m}.
  Proof. destruct m; [left | right]; congruence. Defined.

  Lemma Some_inj {A : Type} {lhs : A} {rhs : A}
    (H_Some_eq : Some lhs = Some rhs)
    : lhs = rhs.
  Proof. congruence. Qed.

  Theorem divmod_inv a b q r (H_b_ne_0 : b <> 0) :
    (a = b * q + r /\ r < b)%nat <->
    (q = (a - r) / b /\ r = a mod b /\ a >= r)%nat.
  Proof with lia || eauto.
    assert (lemma1 := Nat.div_mod).
    enough (lemma2 : forall x y, x > y <-> (exists z, x = S (y + z))). split.
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

  Lemma sub_lt_pos m n : m > 0 -> n > 0 -> m - n < m.
  Proof. intros H1 H2. destruct m, n; try lia. Qed.

  Lemma exp_pos b n : b > 0 -> b ^ n > 0.
  Proof.
    intros.
    induction n.
    - auto.
    - simpl. lia.
  Qed.

  Lemma skipn_exp_length {A} n (xs : list A) : length xs > 0 -> length (skipn (2^n) xs) < length xs.
  Proof.
    intros.
    rewrite skipn_length.
    eapply sub_lt_pos.
    - assumption.
    - eapply exp_pos; lia.
  Qed.

  Lemma tail_length {A} (xs : list A) : length (tail xs) = length xs - 1.
  Proof. destruct xs; simpl; lia || eauto. Qed.

  Lemma removelast_length {A} (xs : list A) : length xs > 0 -> length (removelast xs) = length xs - 1.
  Proof with simpl; try lia.
    revert xs. induction xs using rev_ind...
    rewrite removelast_last, app_length...
  Qed.

  Lemma trim_head_last {A} (xs : list A) : length xs >= 2 -> exists x ys y, xs = [x] ++ ys ++ [y].
  Proof with simpl; lia || eauto.
    destruct xs as [ | x' xs']...
    intros H_len. exists x'. destruct xs' as [ | x'' xs''].
    - inversion H_len...
    - enough (to_show : exists ys y, x'' :: xs'' = ys ++ [y]).
      + destruct to_show as [ys [y H_eq]].
        exists ys, y. apply f_equal...
      + clear x' H_len. revert x''. induction xs'' as [ | x xs IH].
        { intros x'. exists [], x'... }
        { intros x'. destruct (IH x) as [ys [y H_eq]]. exists (x' :: ys), y... apply f_equal... }
  Qed.

  Lemma last_app {A} (xs ys : list A) e : ys <> [] -> last (xs ++ ys) e = last ys e.
  Proof.
    intros. induction xs.
    - reflexivity.
    - simpl. destruct (xs ++ ys) eqn: E.
      + eapply app_eq_nil in E. destruct E. contradiction.
      + assumption.
  Qed.

  Lemma tail_removelast_last {A} (xs : list A) e : length xs >= 2 -> tail (removelast xs) ++ [last xs e] = tail xs.
  Proof.
    intros H. destruct xs as [| x xs] ; simpl in H; try lia.
    assert (H1 : xs <> [])
      by (destruct xs; simpl in H; try lia; discriminate).
    set (H2 := removelast_app [x] H1). simpl app in H2. rewrite H2.
    set (H3 := last_app [x] xs e H1). simpl app in H3. rewrite H3.
    simpl tail.
    symmetry.
    eapply app_removelast_last.
    assumption.
  Qed.

  Lemma In_last {A} (xs : list A) x : xs <> [] -> In (last xs x) xs.
  Proof.
    intros.
    induction xs.
    - contradiction.
    - assert (xs = [] \/ xs <> [])
        by (destruct xs; [ left; reflexivity | right; discriminate ]).
      destruct H0.
      + subst. simpl. auto.
      + replace (last (a :: xs) x) with (last xs x)
          by (rewrite <- (last_app [a] xs x H0); reflexivity).
        simpl. right.
        eapply IHxs; assumption.
  Qed.

  Lemma firstn_exact {A} n (xs ys : list A) : n = length xs -> firstn n (xs ++ ys) = xs.
  Proof.
    intros.
    replace n with (length xs + 0) by lia.
    rewrite firstn_app_2.
    simpl.
    eapply app_nil_r.
  Qed.

  Lemma skipn_exact {A} n (xs ys : list A) : n = length xs -> skipn n (xs ++ ys) = ys.
  Proof.
    intros. subst.
    rewrite skipn_app.
    replace (_ - _) with 0 by lia.
    rewrite skipn_all.
    reflexivity.
  Qed.

  Definition null {A} (xs : list A) : bool :=
    match xs with
    | [] => true
    | _  => false
    end.

  Lemma null_true {A} (xs : list A) : null xs = true <-> xs = [].
  Proof.
    split.
    - destruct xs; [ reflexivity | discriminate ].
    - intros. subst xs. reflexivity.
  Qed.

  Lemma null_false {A} (xs : list A) : null xs = false <-> xs <> [].
  Proof.
    split.
    - destruct xs; discriminate.
    - destruct xs; [ contradiction | reflexivity ].
  Qed.

End Utilities.

Ltac pose_exp2 n :=
  assert (2 ^ n > 0) by (eapply exp_pos; lia).

Ltac dec_nat :=
  match goal with
  | [|- true  = _ ] => symmetry
  | [|- false = _ ] => symmetry
  end;
  match goal with
  | [|- (_ <=? _) = true  ] => eapply leb_correct
  | [|- (_ <=? _) = false ] => eapply leb_correct_conv
  | [|- (_ <?  _) = true  ] => eapply ltb_lt
  | [|- (_ <?  _) = false ] => eapply ltb_ge
  end;
  simpl; lia.

Ltac dec_list :=
  match goal with
  | [|- true  = _ ] => symmetry
  | [|- false = _ ] => symmetry
  end;
  match goal with
  | [|- null _ = true  ] => eapply null_true
  | [|- null _ = false ] =>
    eapply null_false;
    let H := fresh "H" in
    intro H;
    repeat match goal with
           | [ H : (_ ++ _) = [] |- _ ] => eapply app_eq_nil in H; destruct H
           end;
    try discriminate;
    try contradiction
  end.

(* Definition lookup (xs : list A) i := nth_error xs i. *)
Notation lookup xs i := (nth_error xs i).

Section ListOperations.

  Context {A : Type}.

  Definition swap_aux (xs : list A) i1 i2 x i :=
    if Nat.eq_dec i i1 then nth i2 xs x else
    if Nat.eq_dec i i2 then nth i1 xs x else
    x.
  Definition add_indices (xs : list A) := (combine xs (seq 0 (length xs))).
  Definition swap (xs : list A) i j := map (uncurry (swap_aux xs i j)) (add_indices xs).
  Definition upd xs i0 x0 := map (fun '(x, i) => if Nat.eq_dec i i0 then x0 else x) (add_indices xs).

End ListOperations.

Section LList.

  Context {A : Type}.

  Program Fixpoint toLList (n : nat) (xs : list A) {measure (length xs)} : list (list A) :=
    match xs with
    | [] => []
    | _ => firstn (2^n) xs :: toLList (S n) (skipn (2^n) xs)
    end.
  Next Obligation.
    eapply skipn_exp_length.
    destruct xs; try contradiction.
    simpl. lia.
  Defined.

  Lemma unfold_toLList (n : nat) (xs : list A) :
    toLList n xs =
    if null xs
    then []
    else firstn (2^n) xs :: toLList (S n) (skipn (2^n) xs).
  Proof with eauto.
    unfold toLList at 1. unfold toLList_func. rewrite fix_sub_eq.
    - destruct xs...
    - intros [? ?] ? ? ?; simpl. destruct l... apply f_equal...
  Qed.

  Lemma concat_toLList n xs : concat (toLList n xs) = xs.
  Proof.
    remember (length xs) as l.
    revert n xs Heql.
    induction l using Wf_nat.lt_wf_ind.
    intros.
    erewrite unfold_toLList.
    destruct xs.
    - reflexivity.
    - simpl.
      erewrite H.
      3: reflexivity.
      + eapply firstn_skipn.
      + subst.
        eapply skipn_exp_length.
        simpl. lia.
  Qed.

  Global Opaque toLList.

  Fixpoint splitLListLeft (n : nat) (xss : list (list A)) : list (list A) :=
    match xss with
    | [] => []
    | xs :: xss => firstn (2^n) xs :: splitLListLeft (S n) xss
    end.

  Fixpoint splitLListRight (n : nat) (xss : list (list A)) : list (list A) :=
    match xss with
    | [] => []
    | xs :: xss =>
      if length xs <=? 2^n
      then []
      else skipn (2^n) xs :: splitLListRight (S n) xss
    end.

  Fixpoint zipLList (xss yss : list (list A)) : list (list A) :=
    match xss, yss with
    | xs :: xss, ys :: yss => (xs ++ ys) :: zipLList xss yss
    | [], yss => yss
    | xss, [] => xss
    end.

  Lemma zipLList_length (xss yss : list (list A)) :
    length (zipLList xss yss) = max (length xss) (length yss).
  Proof.
    revert yss.
    induction xss as [| xs xss ].
    - reflexivity.
    - intros. simpl.
      destruct yss as [| ys yss ].
      + reflexivity.
      + simpl. rewrite IHxss. reflexivity.
  Qed.

  Lemma splitLListLeft_length n xss : length (splitLListLeft n xss) = length xss.
  Proof.
    revert n.
    induction xss.
    - reflexivity.
    - intros. simpl. rewrite IHxss. reflexivity.
  Qed.

  Lemma splitLListRight_length n xss : length (splitLListRight n xss) <= length xss.
  Proof.
    revert n.
    induction xss.
    - reflexivity.
    - intros. simpl.
      destruct (length a <=? 2^n); simpl.
      + lia.
      + eapply le_n_S.
        eapply IHxss.
  Qed.

  Fixpoint perfect_list (n : nat) (xss : list (list A)) : Prop :=
    match xss with
    | [] => True
    | xs :: xss => length xs = 2^n /\ perfect_list (S n) xss
    end.

  Fixpoint complete_list (n : nat) (xss : list (list A)) : Prop :=
    match xss with
    | [] => True
    | xs :: xss => length xs = 2^n /\ complete_list (S n) xss
                 \/ 0 < length xs < 2^n /\ xss = []
    end.

End LList.

Section BinaryTree.

  Context {A : Type}.

  Inductive bintree : Type :=
  | BT_nil
  | BT_node (x : A) (l r : bintree)
  .

  Inductive bteq_shape : bintree -> bintree -> Prop :=
  | bteq_nil : bteq_shape BT_nil BT_nil
  | bteq_node x l r x' l' r'
              (H_l : bteq_shape l l')
              (H_r : bteq_shape r r')
    : bteq_shape (BT_node x l r) (BT_node x' l' r')
  .

  Inductive btpartial : bintree -> bintree -> Prop :=
  | btpartial_nil : btpartial BT_nil BT_nil
  | btpartial_node x l r l' r'
                   (Hl : btpartial l l')
                   (Hr : btpartial r r')
    : btpartial (BT_node x l r) (BT_node x l' r')
  | btpartial_node' x l r : btpartial (BT_node x l r) BT_nil
  .

  Inductive btin x : bintree -> Prop :=
  | btin_root l r : btin x (BT_node x l r)
  | btin_left y l r : btin x l -> btin x (BT_node y l r)
  | btin_right y l r : btin x r -> btin x (BT_node y l r)
  .

  Definition leaf (t : bintree) : Prop :=
    match t with
    | BT_nil => True
    | BT_node x l r => l = BT_nil /\ r = BT_nil
    end.

  Fixpoint btsize (t : bintree) : nat :=
    match t with
    | BT_nil => 0
    | BT_node x l r => 1 + btsize l + btsize r
    end.

  Fixpoint rank (t : bintree) : nat :=
    match t with
    | BT_nil => 0
    | BT_node x l r => 1 + max (rank l) (rank r)
    end.

  Lemma btsize_eq_1 t : btsize t = 1 ->
                        match t with
                        | BT_nil => False
                        | BT_node x l r => l = BT_nil /\ r = BT_nil
                        end.
  Proof.
    intros.
    destruct t; try discriminate.
    destruct t1; try discriminate.
    destruct t2; try discriminate.
    auto.
  Qed.

End BinaryTree.

Arguments bintree : clear implicits.

Section BinaryTreeIndexing.

  Inductive dir_t : Set := Dir_left | Dir_right.

  Definition btidx := list dir_t.

  Inductive lt_eqlen : btidx -> btidx -> Prop :=
  | lt_eqlen_head i j : length i = length j -> lt_eqlen (Dir_left :: i) (Dir_right :: j)
  | lt_eqlen_cons d i j : lt_eqlen i j -> lt_eqlen (d :: i) (d :: j)
  .

  Definition lt_ltlen (i j : btidx) := length i < length j.

  Definition btidx_lt i j := lt_ltlen i j \/ lt_eqlen i j.

  Definition encodeIdx ds := fold_left (fun i => dir_t_rect (fun _ => nat) (2 * i + 1) (2 * i + 2)) ds 0.

  Lemma _encode_unfold_lemma l n : fold_left (fun i : nat => dir_t_rect (fun _ : dir_t => nat) (i + (i + 0) + 1) (i + (i + 0) + 2)) l n = encodeIdx l + n * 2 ^ (length l).
  Proof.
    revert n.
    induction l.
    - simpl. nia.
    - intros. unfold encodeIdx. destruct a.
      + simpl. rewrite IHl. rewrite IHl.
        rewrite add_0_r. nia.
      + simpl. rewrite IHl. rewrite IHl.
        nia.
  Qed.

  Lemma encode_unfold l:
    encodeIdx l =
      match l with
      | [] => 0
      | Dir_left :: t => encodeIdx t + 2 ^ (length l - 1)
      | Dir_right :: t => encodeIdx t + 2 ^ (length l)
      end.
  Proof.
    destruct l.
    - unfold encodeIdx.
      simpl. auto.
    - destruct d.
      + unfold encodeIdx at 1.
        simpl. rewrite _encode_unfold_lemma. rewrite sub_0_r. nia.
      + unfold encodeIdx at 1.
        simpl. rewrite _encode_unfold_lemma. rewrite add_0_r. nia.
  Qed.

  Lemma encode_inj ds1 ds2
    (H_encode_eq : encodeIdx ds1 = encodeIdx ds2)
    : ds1 = ds2.
  Proof with lia || eauto.
    revert H_encode_eq. unfold encodeIdx; do 2 rewrite <- fold_left_rev_right.
    intros H_eq; apply rev_inj; revert H_eq.
    generalize (rev ds2) as xs2. generalize (rev ds1) as xs1. clear ds1 ds2.
    set (myF := fold_right (fun d i => dir_t_rect (fun _ => nat) (2 * i + 1) (2 * i + 2) d) 0).
    induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl...
    - destruct x2; simpl dir_t_rect...
    - destruct x1; simpl dir_t_rect...
    - destruct x1; destruct x2; simpl dir_t_rect...
      all: intros H_eq; assert (claim1 : myF xs1 = myF xs2)...
      all: apply f_equal...
  Qed.

  Lemma encode_last ds d :
    encodeIdx (ds ++ [d]) =
    match d with
    | Dir_left => 2 * encodeIdx ds + 1
    | Dir_right => 2 * encodeIdx ds + 2
    end.
  Proof.
    unfold encodeIdx at 1. rewrite <- fold_left_rev_right. rewrite rev_unit.
    unfold fold_right. unfold encodeIdx. rewrite <- fold_left_rev_right. destruct d; eauto.
  Qed.

  Lemma decodable i :
    {ds : list dir_t | encodeIdx ds = i}.
  Proof with lia || eauto.
    induction i as [[ | i'] IH] using Wf_nat.lt_wf_rect.
    - exists ([])...
    - set (i := S i').
      destruct (i mod 2) as [ | [ | i_mod_2]] eqn: H_obs.
      + assert (claim1 : i = 2 * ((i - 2) / 2) + 2).
        { apply (positive_even i ((i - 2) / 2))... }
        assert (claim2 : (i - 2) / 2 < i)...
        destruct (IH ((i - 2) / 2) claim2) as [ds H_ds].
        exists (ds ++ [Dir_right]).
        unfold encodeIdx. rewrite fold_left_last. unfold dir_t_rect at 1.
        unfold encodeIdx in H_ds. rewrite H_ds...
      + assert (claim1 : i = 2 * ((i - 1) / 2) + 1).
        { apply (positive_odd i ((i - 1) / 2))... }
        assert (claim2 : (i - 1) / 2 < i)...
        destruct (IH ((i - 1) / 2) claim2) as [ds H_ds].
        exists (ds ++ [Dir_left]).
        unfold encodeIdx. rewrite fold_left_last. unfold dir_t_rect at 1.
        unfold encodeIdx in H_ds. rewrite H_ds...
      + pose (Nat.mod_bound_pos i 2)...
  Defined.

  Definition decodeIdx i := proj1_sig (decodable i).

(* (* Example "decode" *)
  Compute (decode 14).
  (* = [Dir_right; Dir_right; Dir_right] *)
  Compute (decode 15).
  (* = [Dir_left; Dir_left; Dir_left; Dir_left] *)
  Compute (decode 16).
  (* = [Dir_left; Dir_left; Dir_left; Dir_right] *)
*)

  Lemma encode_decode i : encodeIdx (decodeIdx i) = i.
  Proof. exact (proj2_sig (decodable i)). Qed.

  Global Opaque decodeIdx.

  Lemma decode_encode ds : decodeIdx (encodeIdx ds) = ds.
  Proof. apply encode_inj. now rewrite encode_decode with (i := encodeIdx ds). Qed.

End BinaryTreeIndexing.

Notation encode ds := (encodeIdx ds).
Notation decode i := (decodeIdx i).

Section BinaryTreeAccessories.

  Context {A : Type}.

  Definition last_btidx (t : bintree A) := decode (btsize t - 1).

  Definition subtree_init t : option (bintree A) := Some t.

  Definition subtree_step d acc t : option (bintree A) :=
    match t with
    | BT_nil => None
    | BT_node x l r => acc (@dir_t_rect (fun _ => bintree A) l r d)
    end.

  Definition option_subtree := fold_right subtree_step subtree_init.

  Definition subtree_nat t i := option_subtree (decode i) t.

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

  (*
  Definition extract_elements := flat_map (option2list ∘ option_root).

  Definition extract_children := flat_map (@concat (bintree A) ∘ option2list ∘ option_map pair2list ∘ option_children_pair).

  Lemma unfold_extract_elements ts :
    extract_elements ts =
    match ts with
    | [] => []
    | BT_nil :: ts_tail => extract_elements ts_tail
    | BT_node x l r :: ts_tail => x :: extract_elements ts_tail
    end.
  Proof. destruct ts as [ | [ | x l r] ts_tail]; reflexivity. Qed.

  Lemma unfold_extract_children ts :
    extract_children ts =
    match ts with
    | [] => []
    | BT_nil :: ts_tail => extract_children ts_tail
    | BT_node x l r :: ts_tail => [l; r] ++ extract_children ts_tail
    end.
  Proof. destruct ts as [ | [ | x l r] ts_tail]; reflexivity. Qed.
   *)

  Program Fixpoint fromListAux (xss : list (list A)) {measure (length xss)} : bintree A :=
    match xss with
    | [] => BT_nil
    | [] :: xss => BT_nil
    | (x :: xs) :: xss => BT_node x (fromListAux (splitLListLeft 0 xss)) (fromListAux (splitLListRight 0 xss))
    end.
  Next Obligation.
    rewrite splitLListLeft_length. auto.
  Defined.
  Next Obligation.
    simpl.
    set (splitLListRight_length 0 xss).
    lia.
  Defined.

  Lemma unfold_fromListAux xss :
    fromListAux xss =
    match xss with
    | [] => BT_nil
    | [] :: xss => BT_nil
    | (x :: xs) :: xss => BT_node x (fromListAux (splitLListLeft 0 xss)) (fromListAux (splitLListRight 0 xss))
    end.
  Proof with eauto.
    unfold fromListAux at 1; rewrite fix_sub_eq.
    - destruct xss as [ | [ | x xs] xss]...
    - intros [ | [ | ? ?] ?] ? ? ?...
      f_equal...
  Qed.

  Global Opaque fromListAux.

  Definition fromList (xs : list A) : bintree A :=
    fromListAux (toLList 0 xs).

  Fixpoint toListAux (t : bintree A) : list (list A) :=
    match t with
    | BT_nil => []
    | BT_node x l r => [x] :: zipLList (toListAux l) (toListAux r)
    end.

  Lemma unfold_toListAux t :
    toListAux t = match t with
                  | BT_nil => []
                  | BT_node x l r => [x] :: zipLList (toListAux l) (toListAux r)
                  end.
  Proof. destruct t; reflexivity. Qed.

  Definition toList root := concat (toListAux root).

  Definition upd_root (x : A) t :=
    match t with
    | BT_nil => BT_nil
    | BT_node _ l r => BT_node x l r
    end.

End BinaryTreeAccessories.

Section CompleteBinaryTree.

  Context {A : Type}.

  Inductive perfect' : bintree A -> nat -> Prop :=
  | perfect_nil : perfect' BT_nil O
  | perfect_node {n : nat} x l r
                 (H_l : perfect' l n)
                 (H_r : perfect' r n)
    : perfect' (BT_node x l r) (S n)
  .

  Inductive complete' : bintree A -> nat -> Prop :=
  | complete_nil
    : complete' BT_nil O
  | complete_node_perfect_complete {n : nat} x l r
                                   (H_l : perfect' l n)
                                   (H_r : complete' r n)
    : complete' (BT_node x l r) (S n)
  | complete_node_complete_perfect {n : nat} x l r
                                   (H_l : complete' l (S n))
                                   (H_r : perfect' r n)
    : complete' (BT_node x l r) (S (S n))
  .

  Definition perfect t := exists n, perfect' t n.
  Definition complete t := exists n, complete' t n.

End CompleteBinaryTree.

(* (* Example "toList" *)
  Compute (toList (BT_node 1 (BT_node 2 (BT_node 4 (BT_node 8 BT_nil BT_nil) (BT_node 9 BT_nil BT_nil)) (BT_node 5 (BT_node 10 BT_nil BT_nil) (BT_node 11 BT_nil BT_nil))) (BT_node 3 (BT_node 6 (BT_node 12 BT_nil BT_nil) (BT_node 13 BT_nil BT_nil)) (BT_node 7 (BT_node 14 BT_nil BT_nil) (BT_node 15 BT_nil BT_nil))))).
  (* = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] *)
  Compute (toList (BT_node 1 (BT_node 2 (BT_node 4 (BT_node 8 BT_nil BT_nil) (BT_node 9 BT_nil BT_nil)) (BT_node 5 (BT_node 10 BT_nil BT_nil) (BT_node 11 BT_nil BT_nil))) (BT_node 3 (BT_node 6 (BT_node 12 BT_nil BT_nil) (BT_node 13 BT_nil BT_nil)) (BT_node 7 (BT_node 14 BT_nil BT_nil) BT_nil)))).
  (* = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14] *)
*)

(*
 (* Example "fromList" *)
  Compute (fromList [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]).
  (* = BT_node 1
         (BT_node 2
            (BT_node 4 (BT_node 8 BT_nil BT_nil) (BT_node 9 BT_nil BT_nil))
            (BT_node 5 (BT_node 10 BT_nil BT_nil) (BT_node 11 BT_nil BT_nil)))
         (BT_node 3
            (BT_node 6 (BT_node 12 BT_nil BT_nil) (BT_node 13 BT_nil BT_nil))
            (BT_node 7 (BT_node 14 BT_nil BT_nil) (BT_node 15 BT_nil BT_nil)))
  *)
  Compute (fromList [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]).
  (* = BT_node 1
         (BT_node 2
            (BT_node 4 (BT_node 8 BT_nil BT_nil) (BT_node 9 BT_nil BT_nil))
            (BT_node 5 (BT_node 10 BT_nil BT_nil) (BT_node 11 BT_nil BT_nil)))
         (BT_node 3
            (BT_node 6 (BT_node 12 BT_nil BT_nil) (BT_node 13 BT_nil BT_nil))
            (BT_node 7 (BT_node 14 BT_nil BT_nil) BT_nil))
  *)
*)

Section HeapProperty.

  Context {A : Type}.
  Variable R : A -> A -> Prop.

  Inductive heap : bintree A -> Prop :=
  | heap_nil
    : heap BT_nil
  | heap_node x l r
    (R_x_l : @option_rect A (fun _ => Prop) (R x) (True) (option_root l))
    (R_x_r : @option_rect A (fun _ => Prop) (R x) (True) (option_root r))
    (heap_l : heap l)
    (heap_r : heap r)
    : heap (BT_node x l r).

  Inductive heap_pr (p : A) : bintree A -> Prop :=
  | heap_pr_nil : heap_pr p BT_nil
  | heap_pr_node x l r
               (R_p_x : R p x)
               (R_x_l : @option_rect A (fun _ => Prop) (R x) True (option_root l))
               (R_x_r : @option_rect A (fun _ => Prop) (R x) True (option_root r))
               (heap_l : heap l)
               (heap_r : heap r)
    : heap_pr p (BT_node x l r)
  .

  Definition heap_at j t : Prop :=
    match subtree_nat t j with
    | None => True
    | Some t' => heap t'
    end.

End HeapProperty.

Section BinaryTreeZipper.

  Context {A : Type}.

  Inductive btctx : Type :=
  | btctx_top: btctx
  | btctx_left (x : A) (r : bintree A) (g : btctx) : btctx
  | btctx_right (x : A) (l : bintree A) (g : btctx) : btctx
  .

  Fixpoint btctx2idx (g : btctx) : btidx :=
    match g with
    | btctx_top => []
    | btctx_left _ _ g => btctx2idx g ++ [Dir_left]
    | btctx_right _ _ g => btctx2idx g ++ [Dir_right]
    end.

  Fixpoint recover_bintree (g : btctx) (t : bintree A) : bintree A :=
    match g with
    | btctx_top => t
    | btctx_left x r g => recover_bintree g (BT_node x t r)
    | btctx_right x l g => recover_bintree g (BT_node x l t)
    end.

  Fixpoint focus (g : btctx) (t : bintree A) (i : btidx) : btctx * bintree A :=
    match t, i with
    | _, [] => (g, t)
    | BT_nil, _ :: _ => (g, BT_nil)
    | BT_node x l r, Dir_left :: j => focus (btctx_left x r g) l j
    | BT_node x l r, Dir_right :: j => focus (btctx_right x l g) r j
    end.

End BinaryTreeZipper.

Arguments btctx : clear implicits.
