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

  Definition option2list {A : Type} : option A -> list A :=
    @option_rect A (fun _ => list A) (fun x => [x]) [].

  Definition pair2list {A : Type} : A * A -> list A :=
    fun '(x1, x2) => [x1; x2].

  Definition isSome {A : Type} : option A -> Prop := fun m => m <> None.

  Definition isNone {A : Type} : option A -> Prop := fun m => m = None.

  Lemma Some_or_None {A : Type} : forall m : option A,  {isSome m} + {isNone m}.
  Proof. destruct m; [left | right]; congruence. Qed.

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

  Lemma tail_length {A} (xs : list A) : length xs > 0 -> length (tail xs) = length xs - 1.
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
  Definition upd xs i0 x0 := map (fun '(x, i) => if Nat.eq_dec i i0 then x0 else x) (add_indices xs).

  Program Fixpoint trim_exp (n : nat) (xs : list A) {measure (length xs)} : list (list A) :=
    match xs with
    | [] => []
    | _ => firstn (2^n) xs :: trim_exp (S n) (skipn (2^n) xs)
    end.
  Next Obligation.
    eapply skipn_exp_length.
    destruct xs; try contradiction.
    simpl. lia.
  Defined.

  Lemma unfold_trim_exp (n : nat) (xs : list A) :
    trim_exp n xs =
    match xs with
    | [] => []
    | _ => firstn (2^n) xs :: trim_exp (S n) (skipn (2^n) xs)
    end.
  Proof with eauto.
    unfold trim_exp at 1. unfold trim_exp_func. rewrite fix_sub_eq.
    - destruct xs...
    - intros [? ?] ? ? ?; simpl. destruct l... apply f_equal...
  Qed.

  Lemma concat_trim_exp n xs : concat (trim_exp n xs) = xs.
  Proof.
    remember (length xs) as l.
    revert n xs Heql.
    induction l using Wf_nat.lt_wf_ind.
    intros.
    erewrite unfold_trim_exp.
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

  Global Opaque trim_exp.

  Fixpoint split_exp_left (n : nat) (xss : list (list A)) : list (list A) :=
    match xss with
    | [] => []
    | xs :: xss => firstn (2^n) xs :: split_exp_left (S n) xss
    end.

  Fixpoint split_exp_right (n : nat) (xss : list (list A)) : list (list A) :=
    match xss with
    | [] => []
    | xs :: xss =>
      if length xs <=? 2^n
      then []
      else skipn (2^n) xs :: split_exp_right (S n) xss
    end.

  Fixpoint zip_exp (xss yss : list (list A)) : list (list A) :=
    match xss, yss with
    | xs :: xss, ys :: yss => (xs ++ ys) :: zip_exp xss yss
    | [], yss => yss
    | xss, [] => xss
    end.

  Lemma split_exp_left_length n xss : length (split_exp_left n xss) = length xss.
  Proof.
    revert n.
    induction xss.
    - reflexivity.
    - intros. simpl. rewrite IHxss. reflexivity.
  Qed.

  Lemma split_exp_right_length n xss : length (split_exp_right n xss) <= length xss.
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

  Fixpoint complete_list (n : nat) (xss : list (list A)) : Prop :=
    match xss with
    | [] => True
    | xs :: xss => length xs = 2^n /\ complete_list (S n) xss
                 \/ 0 < length xs < 2^n /\ xss = []
    end.

  Lemma complete_trim n xs : complete_list n (trim_exp n xs).
  Proof with lia || eauto.
    remember (length xs) as l.
    revert n xs Heql.
    induction l as [l IH] using Wf_nat.lt_wf_ind.
    intros n [ | x xs'].
    - intros Heql. now rewrite unfold_trim_exp.
    - set (xs := x :: xs'). intros Heql.
      rewrite unfold_trim_exp. unfold xs at 1. simpl.
      assert (claim1 : length (firstn (2^n) xs) = min (2^n) l).
      { rewrite Heql. apply firstn_length. }
      assert (claim2 : length (firstn (2 ^ n) xs) = 2 ^ n \/ length (firstn (2 ^ n) xs) < 2 ^ n) by lia.
      assert (claim3 : l > 0).
      { rewrite Heql. unfold xs. simpl... }
      assert (claim4 : 2^n > 0) by now apply exp_pos; lia.
      destruct claim2 as [claim2 | claim2]; [left | right].
      + split... eapply IH; try reflexivity. rewrite Heql.
        apply skipn_exp_length. simpl...
      + split...
        assert (claim5 : length (skipn (2 ^ n) xs) = 0).
        { rewrite skipn_length... }
        destruct (skipn (2 ^ n) xs)...
        inversion claim5.
  Qed.

  Lemma split_zip n xss : complete_list (S n) xss -> zip_exp (split_exp_left n xss) (split_exp_right n xss) = xss.
    revert n.
    induction xss as [| xs xss ].
    - reflexivity.
    - intros.
      Opaque pow.
      simpl in H.
      Transparent pow.
      destruct H; destruct H.
      + simpl.
        assert (2 ^ n > 0)
          by (eapply exp_pos; lia).
        assert ((length xs <=? 2^n) = false)
          by (eapply leb_correct_conv; simpl in H; lia).
        rewrite H2.
        rewrite firstn_skipn.
        rewrite IHxss by assumption.
        reflexivity.
      + subst. simpl.
        remember (length xs <=? 2^n).
        destruct b.
        * rewrite firstn_all2.
          reflexivity.
          eapply leb_complete.
          auto.
        * rewrite firstn_skipn.
          reflexivity.
  Qed.

  Lemma complete_split_left n xss : complete_list (S n) xss -> complete_list n (split_exp_left n xss).
  Proof with lia || eauto.
    revert n; induction xss as [ | xs xss IH]...
    intros n H_complete. simpl complete_list in H_complete.
    assert (claim1 : length (firstn (2^n) xs) = min (2^n) (length xs)).
    { apply firstn_length. }
    assert (claim2 : 2^n > 0).
    { apply exp_pos... }
    destruct H_complete as [[H_length H_complete] | [H_length H_nil]]; simpl.
    - left. split...
    - assert (claim3 : length (firstn (2 ^ n) xs) = 2^n \/ length (firstn (2 ^ n) xs) <2^n)...
      destruct claim3 as [claim3 | claim3].
      + left. split... apply IH. now rewrite H_nil.
      + right. split... rewrite H_nil...
  Qed.

  Lemma complete_split_right n xss : complete_list (S n) xss -> complete_list n (split_exp_right n xss).
  Proof with lia || eauto.
    revert n; induction xss as [ | xs xss IH]...
    intros n H_complete. simpl complete_list in H_complete.
    simpl. destruct (length xs <=? 2 ^ n) eqn: H_obs; simpl...
    assert (claim1 : length xs > 2 ^ n).
    { rewrite leb_nle in H_obs... }
    destruct H_complete as [[H_length H_complete] | [H_length H_nil]]; simpl.
    - left. split... rewrite skipn_length...
    - rewrite H_nil. right. split... rewrite skipn_length...
  Qed.

End ListOperations.

Section BinaryTree.

  Context {A : Type}.

  Inductive bintree : Type :=
  | BT_nil
  | BT_node (x : A) (l r : bintree)
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

  Definition encode ds := fold_left (fun i => dir_t_rect (fun _ => nat) (2 * i + 1) (2 * i + 2)) ds 0.

  Lemma _encode_unfold_lemma l n : fold_left (fun i : nat => dir_t_rect (fun _ : dir_t => nat) (i + (i + 0) + 1) (i + (i + 0) + 2)) l n = encode l + n * 2 ^ (length l).
  Proof.
    revert n.
    induction l.
    - simpl. nia.
    - intros. unfold encode. destruct a.
      + simpl. rewrite IHl. rewrite IHl.
        rewrite add_0_r. nia.
      + simpl. rewrite IHl. rewrite IHl.
        nia.
  Qed.

  Lemma encode_unfold l:
    encode l =
      match l with
      | [] => 0
      | Dir_left :: t => encode t + 2 ^ (length l - 1)
      | Dir_right :: t => encode t + 2 ^ (length l)
      end.
  Proof.
    destruct l.
    - unfold encode.
      simpl. auto.
    - destruct d.
      + unfold encode at 1.
        simpl. rewrite _encode_unfold_lemma. rewrite sub_0_r. nia.
      + unfold encode at 1.
        simpl. rewrite _encode_unfold_lemma. rewrite add_0_r. nia.
  Qed.

  Lemma encode_inj ds1 ds2
    (H_encode_eq : encode ds1 = encode ds2)
    : ds1 = ds2.
  Proof with lia || eauto.
    revert H_encode_eq. unfold encode; do 2 rewrite <- fold_left_rev_right.
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
    encode (ds ++ [d]) =
    match d with
    | Dir_left => 2 * encode ds + 1
    | Dir_right => 2 * encode ds + 2
    end.
  Proof.
    unfold encode at 1. rewrite <- fold_left_rev_right. rewrite rev_unit.
    unfold fold_right. unfold encode. rewrite <- fold_left_rev_right. destruct d; eauto.
  Qed.

  Lemma decodable i :
    {ds : list dir_t | encode ds = i}.
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
        unfold encode. rewrite fold_left_last. unfold dir_t_rect at 1.
        unfold encode in H_ds. rewrite H_ds...
      + assert (claim1 : i = 2 * ((i - 1) / 2) + 1).
        { apply (positive_odd i ((i - 1) / 2))... }
        assert (claim2 : (i - 1) / 2 < i)...
        destruct (IH ((i - 1) / 2) claim2) as [ds H_ds].
        exists (ds ++ [Dir_left]).
        unfold encode. rewrite fold_left_last. unfold dir_t_rect at 1.
        unfold encode in H_ds. rewrite H_ds...
      + pose (Nat.mod_bound_pos i 2)...
  Defined.

  Definition decode i := proj1_sig (decodable i).

(* (* Example "decode" *)
  Compute (decode 14).
  (* = [Dir_right; Dir_right; Dir_right] *)
  Compute (decode 15).
  (* = [Dir_left; Dir_left; Dir_left; Dir_left] *)
  Compute (decode 16).
  (* = [Dir_left; Dir_left; Dir_left; Dir_right] *)
*)

  Lemma encode_decode i : encode (decode i) = i.
  Proof. exact (proj2_sig (decodable i)). Qed.

  Global Opaque decode.

  Lemma decode_encode ds : decode (encode ds) = ds.
  Proof. apply encode_inj. now rewrite encode_decode with (i := encode ds). Qed.

  Lemma unfold_decode i :
    decode i =
    if Nat.eq_dec i 0 then [] else
    if Nat.eq_dec (i mod 2) 1
    then decode ((i - 1) / 2) ++ [Dir_left]
    else decode ((i - 2) / 2) ++ [Dir_right].
  Proof with lia || discriminate || eauto.
    apply encode_inj. rewrite encode_decode.
    destruct (Nat.eq_dec i 0) as [H_yes1 | H_no1]...
    assert (claim1 := Nat.mod_bound_pos i 2).
    destruct (Nat.eq_dec (i mod 2) 1) as [H_yes2 | H_no2];
      [assert (claim2 := encode_decode ((i - 1) / 2)) | assert (claim2 := encode_decode ((i - 2) / 2))].
    all: symmetry; revert claim2; unfold encode; intros H_eq;
      rewrite fold_left_last; unfold dir_t_rect at 1;
      rewrite H_eq; symmetry.
    - apply positive_odd...
    - apply positive_even...
  Qed.

  Lemma decode_nat n :
    match decode n with
    | [] => n = 0
    | Dir_left :: l => encode l = n - 2 ^ (length (decode n)-1)
    | Dir_right :: l => encode l = n - 2 ^ (length (decode n))
    end.
  Proof with auto.
    destruct (decode n) eqn:E.
    - apply (f_equal encode) in E;rewrite (encode_decode n) in E.
      unfold encode in E; simpl in E...
    - apply (f_equal encode) in E;rewrite (encode_decode n) in E;rewrite E.
      rewrite (encode_unfold (d :: l)). destruct d;simpl;nia.
  Qed.

  Lemma nat_btidx_iff i j : btidx_lt i j <-> encode i < encode j.
  Admitted.
      
End BinaryTreeIndexing.

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

  Lemma unfold_option_subtree ds t :
    option_subtree ds t =
    match ds with
    | [] => Some t
    | d :: ds' =>
      match t with
      | BT_nil => None
      | BT_node x l r => option_subtree ds' (dir_t_rect (fun _ => bintree A) l r d)
      end
    end.
  Proof. induction ds as [ | [ | ] ds IH]; eauto. Qed.

  Lemma option_subtree_last ds d :
    forall root,
    option_subtree (ds ++ [d]) root =
    match option_subtree ds root with
    | None => None
    | Some t => 
      match t with
      | BT_nil => None
      | BT_node x l r => Some (dir_t_rect (fun _ => bintree A) l r d)
      end
    end.
  Proof.
    enough (claim1 : option_subtree (ds ++ [d]) = fold_right subtree_step (subtree_step d subtree_init) ds).
    - rewrite claim1. clear claim1. unfold option_subtree. induction ds; destruct d; destruct root; eauto.
    - unfold option_subtree at 1. rewrite <- rev_involutive with (l := ds ++ [d]) at 1.
      rewrite fold_left_rev_right, rev_unit. simpl. now rewrite <- fold_left_rev_right, rev_involutive.
  Qed.

  Inductive occurs (t : bintree A) : list dir_t -> bintree A -> Prop :=
  | Occurs_0
    : occurs t [] t
  | Occurs_l ds x l r
    (H_l : occurs t ds l)
    : occurs t (Dir_left :: ds) (BT_node x l r)
  | Occurs_r ds x l r
    (H_r : occurs t ds r)
    : occurs t (Dir_right :: ds) (BT_node x l r).

  Local Hint Constructors occurs : core.

  Lemma occurs_iff ds t root :
    occurs t ds root <->
    option_subtree ds root = Some t.
  Proof with discriminate || eauto.
    split. intros X; induction X... revert t root.
    induction ds as [ | [ | ] ds IH]; simpl; intros t root H_eq.
    { apply Some_inj in H_eq; subst... }
    all: destruct root as [ | x l r]...
  Qed.

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

  Program Fixpoint fromListAux (xss : list (list A)) {measure (length xss)} : bintree A :=
    match xss with
    | [] => BT_nil
    | [] :: xss => BT_nil
    | (x :: xs) :: xss => BT_node x (fromListAux (split_exp_left 0 xss)) (fromListAux (split_exp_right 0 xss))
    end.
  Next Obligation.
    rewrite split_exp_left_length. auto.
  Defined.
  Next Obligation.
    simpl.
    set (split_exp_right_length 0 xss).
    lia.
  Defined.

  Lemma unfold_fromListAux xss :
    fromListAux xss =
    match xss with
    | [] => BT_nil
    | [] :: xss => BT_nil
    | (x :: xs) :: xss => BT_node x (fromListAux (split_exp_left 0 xss)) (fromListAux (split_exp_right 0 xss))
    end.
  Proof with eauto.
    unfold fromListAux at 1; rewrite fix_sub_eq.
    - destruct xss as [ | [ | x xs] xss]...
    - intros [ | [ | ? ?] ?] ? ? ?...
      f_equal...
  Qed.

  Global Opaque fromListAux.

  Definition fromList (xs : list A) : bintree A :=
    fromListAux (trim_exp 0 xs).

  Fixpoint toListAux (t : bintree A) : list (list A) :=
    match t with
    | BT_nil => []
    | BT_node x l r => [x] :: zip_exp (toListAux l) (toListAux r)
    end.

  Lemma unfold_toListAux t :
    toListAux t = match t with
                  | BT_nil => []
                  | BT_node x l r => [x] :: zip_exp (toListAux l) (toListAux r)
                  end.
  Proof. destruct t; reflexivity. Qed.

  Definition toList root := concat (toListAux root).

  Lemma toListAux_fromListAux xss : complete_list 0 xss -> toListAux (fromListAux xss) = xss.
  Proof.
    remember (length xss) as l eqn: H.
    revert xss H.
    induction l using Wf_nat.lt_wf_ind.
    - rename H into IH. intros xss H1 H2.
      destruct xss as [|xs xss]; auto.
      destruct xs as [|x xs]; simpl in H2.
      + destruct H2; destruct H; lia.
      + destruct H2; destruct H; assert (xs = [])
          by (eapply length_zero_iff_nil; lia);
        subst; try reflexivity.
        rewrite unfold_fromListAux.
        simpl.
        erewrite IH with (xss := split_exp_left 0 xss); try reflexivity.
        erewrite IH with (xss := split_exp_right 0 xss); try reflexivity.
        rewrite split_zip by assumption.
        reflexivity.
        * assert (length (split_exp_right 0 xss) <= length xss)
            by eapply split_exp_right_length.
          simpl. lia.
        * eapply complete_split_right; assumption.
        * rewrite split_exp_left_length. simpl. lia.
        * eapply complete_split_left; assumption.
  Qed.

  Lemma toList_fromList xs : toList (fromList xs) = xs.
  Proof.
    unfold fromList, toList.
    rewrite toListAux_fromListAux by eapply complete_trim.
    eapply concat_trim_exp.
  Qed.

  Lemma toList_length t : length (toList t) = btsize t.
  Proof.
    unfold toList. induction t.
    - simpl. auto.
    - simpl. rewrite <- IHt1. rewrite <- IHt2.
      apply f_equal. remember (toListAux t1) as xss1. remember (toListAux t2) as xss2.
      clear IHt1 IHt2 Heqxss1 Heqxss2.
      revert xss2. induction xss1.
      + simpl. auto.
      + intros. destruct xss2.
        * simpl. nia.
        * simpl. rewrite app_length. rewrite IHxss1.
          do 3 rewrite app_length. nia.
  Qed.

  Lemma toList_step t : btsize t >= 1 -> match t with
                                       | BT_nil => False
                                       | BT_node x _ _ => toList t = x :: tail (toList t)
                                       end.
  Proof.
    intros.
    destruct t; simpl in H; try lia.
    reflexivity.
  Qed.

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

  Definition complete t := exists n, complete' t n.

  Lemma perfect'2complete' {n} t
    (H_perfect : perfect' t n)
    : complete' t n.
  Proof.
    induction H_perfect as [ | n x l r H_l IH_l H_r IH_r].
    - exact (complete_nil).
    - exact (complete_node_perfect_complete x l r H_l IH_r).
  Qed.

  Lemma complete_ind_ranked (P : bintree A -> nat -> Prop) :
    P BT_nil 0 ->
    (forall x l r n_l n_r, (n_r = n_l \/ S n_r = n_l) ->
                      complete' l n_l -> complete' r n_r ->
                      P l n_l -> P r n_r ->
                      P (BT_node x l r) (S n_l)) ->
    forall t n, complete' t n -> P t n.
  Proof.
    intros H_base H_ind t n H_complete.
    revert t H_complete.
    induction n using Wf_nat.lt_wf_ind.
    intros t H_complete.
    destruct H_complete as [| n x l r H_l H_r | n x l r H_l H_r ].
    - exact H_base.
    - assert (H_l' : complete' l n) by (eapply perfect'2complete'; assumption).
      eapply H_ind.
      + left. reflexivity.
      + assumption.
      + assumption.
      + eapply H; try lia; assumption.
      + eapply H; try lia; assumption.
    - assert (H_r' : complete' r n) by (eapply perfect'2complete'; assumption).
      eapply H_ind.
      + right. reflexivity.
      + assumption.
      + assumption.
      + eapply H; try lia; assumption.
      + eapply H; try lia; assumption.
  Qed.

  Lemma complete_ind_unranked (P : bintree A -> Prop) :
    P BT_nil ->
    (forall x l r, complete l -> complete r -> P l -> P r -> P (BT_node x l r)) ->
    forall t, complete t -> P t.
  Proof.
    set (P' := fun t (n : nat) => P t).
    intros H_base H_ind t H_complete.
    destruct H_complete as [n H_complete].
    eapply complete_ind_ranked with (P := P').
    - exact H_base.
    - intros. eapply H_ind.
      + eexists. eassumption.
      + eexists. eassumption.
      + assumption.
      + assumption.
    - eassumption.
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
  Definition last_index (t : bintree A) := decode (btsize t - 1).

  Lemma perfect'_rank t n
    (H_perfect : perfect' t n)
    : rank t = n.
  Proof. induction H_perfect; simpl; lia. Qed.

  Lemma complete'_rank t n
    (H_complete : complete' t n)
    : rank t = n.
  Proof. induction H_complete. 2: apply perfect'_rank in H_l. 3: apply perfect'_rank in H_r. all: simpl; lia. Qed.

  Lemma perf_size t n :
    perfect' t n ->
    btsize t = 2 ^ n -1.
  Proof.
    intros. induction H;auto.
    simpl. rewrite IHperfect'1. rewrite IHperfect'2.
    assert (2 ^ n > 0) by (apply exp_pos;nia). nia.
  Qed.

  Lemma comp_size t n :
    complete' t (S n) ->
    2 ^ n <= btsize t <= 2 ^ (S n) - 1.
  Proof.
    revert t. induction n;intros.
    - inversion H;subst. simpl. inversion H_l;subst. inversion H_r;subst. simpl. auto.
    - inversion H;subst.
      + apply perf_size in H_l. simpl. rewrite H_l.
        rewrite <- add_succ_l. assert (2 ^ n > 0) by (apply exp_pos;nia).
        replace (S (2 ^ n -1)) with (2 ^ n) by nia.
        assert (btsize r <= 2 ^ S n - 1).
        * clear IHn H0 H_l H l x. induction H_r using complete_ind_ranked;simpl.
          ** assert (2 ^ n >0) by (apply exp_pos;nia). nia.
          ** destruct H;subst.
             *** assert (2 ^ n_l > 0) by (apply exp_pos;nia).
                 nia.
             *** simpl in *. assert (2 ^ n_r > 0) by (apply exp_pos;nia).
                 nia.
        * simpl in *. nia.
      + apply perf_size in H_r. simpl. rewrite H_r.
        rewrite <- add_succ_r.
        apply IHn in H_l.
        assert (2 ^ n > 0) by (apply exp_pos;nia).
        replace (S (2 ^ n - 1)) with (2 ^ n) by nia.
        simpl in *. nia.
  Qed.
  
  Lemma encode_bound l n : length l = n -> 2^n -1 <= encode l < 2 ^ (S n) -1.
  Proof.
    revert n. induction l;intros.
    - simpl in *. rewrite <- H. simpl. auto.
    - simpl in *. destruct n;inversion H.
      rewrite encode_unfold. destruct a.
      + simpl. rewrite H1. apply IHl in H1. rewrite sub_0_r.
        assert (2 ^ n > 0) by (apply exp_pos;nia). nia.
      + simpl. rewrite H1. apply IHl in H1.
        assert (2 ^ n > 0) by (apply exp_pos;nia). nia.
  Qed.
  
  Lemma decode_ubound j n : j < 2 ^ n - 1 -> length (decode j) < n.
  Proof.
    remember (decode j) as l. revert Heql. revert j.
    induction l;intros.
    - destruct n;inversion H.    
  Admitted.

  Lemma decode_lbound j n : 2 ^ n -1 <= j -> n <= length (decode j).
  Admitted.

  Lemma toList_lookup root i t
    (H_bound : i < length (toList root))
    (H_complete : complete root)
    (H_occurs : occurs t (decode i) root)
    : lookup (toList root) i = option_root t.
  Proof.
  Admitted.

  Lemma last_btidx_nil : last_btidx (BT_nil : bintree A) = [].
  Proof. reflexivity. Qed.

  Lemma last_btidx_perfect_complete x l r n :
    n > 0 ->
    perfect' l n ->
    complete' r n ->
    last_btidx (BT_node x l r) = Dir_right :: last_btidx r.
  Proof.
    intros. unfold last_btidx. simpl. rewrite sub_0_r.
    apply encode_inj. rewrite (encode_decode _).
    rewrite encode_unfold. rewrite (encode_decode _). simpl length.
    rewrite (perf_size _ _ H0).
    destruct n.
    - inversion H.
    - apply comp_size in H1. destruct H1. pose proof H1 as R.
      eapply sub_le_mono_r with (p:=1) in H1.
      eapply sub_le_mono_r with (p:=1) in H2.
      apply decode_lbound in H1.
      assert (btsize r -1 < 2 ^ S n -1).
      + apply Lt.le_lt_n_Sm in H2.  rewrite <- sub_succ_l in H2.
        2 :{simpl. pose proof (exp_pos 2). assert (B : 2>0) by nia.
            apply H3 with (n:=n) in B. nia. }
        replace (S (2 ^ S n - 1) - 1) with (2 ^ S n - 1) in H2 by nia. auto.
      + apply decode_ubound in H3. assert (length (decode (btsize r - 1)) = n) by nia.
        rewrite H4. simpl. assert (B : 2 > 0) by nia. pose proof (exp_pos 2 n B).
        nia.
  Qed.
    
  Lemma last_btidx_complete_perfect x l r n :
    complete' l (S n) ->
    perfect' r n ->
    last_btidx (BT_node x l r) = Dir_left :: last_btidx l.
  Proof.
    intros. unfold last_btidx. simpl. rewrite sub_0_r.
    apply encode_inj. rewrite (encode_decode _).
    rewrite encode_unfold. rewrite (encode_decode _). simpl length.
    rewrite (perf_size _ _ H0).
    apply comp_size in H. destruct H. pose proof H1 as R. pose proof H as T.
    apply sub_le_mono_r with (p:=1) in H.
    apply sub_le_mono_r with (p:=1) in H1.
    apply decode_lbound in H.
    assert (2 ^ n > 0) by (apply exp_pos;auto).
    assert (2 ^ S n >= 2) by (simpl;nia).
    assert (btsize l - 1 < 2 ^ S n - 1) by nia.
    apply decode_ubound in H4. assert (length (decode (btsize l -1)) = n) by nia.
    rewrite H5. simpl. rewrite sub_0_r. nia.
  Qed.

  Lemma complete'_last_btidx_length t n :
    complete' t n ->
    length (last_btidx t) = n - 1.
  Proof.
    intros H.
    induction H as [| n x l r H_l H_r | n x l r H_l H_r].
    - reflexivity.
    - destruct n.
      + inversion H_l.
        inversion H_r.
        subst.
        reflexivity.
      + erewrite last_btidx_perfect_complete with (n := S n)
          by (try lia; eassumption).
        simpl.
        lia.
    - erewrite last_btidx_complete_perfect
        by eassumption.
      simpl.
      lia.
  Qed.

  Lemma subtree_outrange_ltlen (t : bintree A) :
    complete t ->
    forall j, lt_ltlen (last_btidx t) j ->
         option_subtree j t = Some BT_nil \/ option_subtree j t = None.
  Proof.
    unfold lt_ltlen in *.
    intros H j Hj.
    destruct H as [n H].
    revert t H j Hj.
    induction n using Wf_nat.lt_wf_ind; rename H into IH.
    intros t H j Hj.
    destruct H.
    - destruct j; auto.
    - destruct n.
      { inversion H_l.
        inversion H.
        subst.
        unfold last_btidx in Hj; rewrite unfold_decode in Hj; simpl in Hj.
        destruct j; simpl in Hj; try lia.
        destruct j as [| d' j].
        - left. destruct d; reflexivity.
        - right. destruct d; reflexivity.
      }
      erewrite last_btidx_perfect_complete with (n := S n) in Hj by (try lia; eassumption).
      destruct j as [|[] j]; simpl in Hj.
      + lia.
      + rewrite unfold_option_subtree; simpl.
        erewrite complete'_last_btidx_length in Hj by eassumption.
        eapply (IH (S n)).
        * lia.
        * eapply perfect'2complete'. eassumption.
        * erewrite complete'_last_btidx_length
            by (eapply perfect'2complete'; eassumption).
          lia.
      + rewrite unfold_option_subtree; simpl.
        eapply (IH (S n)).
        * lia.
        * eassumption.
        * lia.
    - erewrite last_btidx_complete_perfect in Hj by eassumption.
      destruct j as [|[] j]; simpl in Hj.
      + lia.
      + rewrite unfold_option_subtree; simpl.
        eapply (IH (S n)).
        * lia.
        * eassumption.
        * lia.
      + rewrite unfold_option_subtree; simpl.
        erewrite complete'_last_btidx_length in Hj by eassumption.
        eapply (IH n).
        * lia.
        * eapply perfect'2complete'. eassumption.
        * erewrite complete'_last_btidx_length
            by (eapply perfect'2complete'; eassumption).
          lia.
  Qed.

  (* It's possible to prove option_subtree j t = Some BT_nil *)
  Lemma subtree_outrange_eqlen (t : bintree A) :
    complete t ->
    forall j, lt_eqlen (last_btidx t) j ->
         option_subtree j t = Some BT_nil \/ option_subtree j t = None.
  Proof.
    intros H j Hj.
    destruct H as [n H].
    revert t H j Hj.
    induction n using Wf_nat.lt_wf_ind; rename H into IH.
    intros t H j Hj.
    destruct H.
    - rewrite last_btidx_nil in Hj.
      inversion Hj.
    - destruct n.
      { inversion H_l.
        inversion H.
        subst.
        unfold last_btidx in Hj; rewrite unfold_decode in Hj; simpl in Hj.
        inversion Hj.
      }
      erewrite last_btidx_perfect_complete with (n := S n) in Hj by (try lia; eassumption).
      inversion Hj; subst.
      rewrite unfold_option_subtree; simpl.
      eapply (IH (S n)); try assumption; lia.
    - erewrite last_btidx_complete_perfect in Hj by eassumption.
      inversion Hj; subst.
      + rewrite unfold_option_subtree; simpl.
        destruct n.
        { inversion H_r.
          inversion H.
          inversion H_l.
          inversion H_r0.
          subst.
          destruct j0; try discriminate.
          auto.
        }
        eapply subtree_outrange_ltlen.
        * eexists. eapply perfect'2complete'. eassumption.
        * unfold lt_ltlen.
          rewrite <- H1.
          erewrite complete'_last_btidx_length
            by (eapply perfect'2complete'; eassumption).
          erewrite complete'_last_btidx_length
            by eassumption.
          lia.
      + rewrite unfold_option_subtree; simpl.
        eapply (IH (S n)); try eassumption; lia.
  Qed.

  Lemma subtree_outrange j (t : bintree A) :
    complete t -> j >= btsize t ->
    subtree_nat t j = Some BT_nil \/ subtree_nat t j = None.
  Proof.
    intros.
    destruct H.
    destruct t eqn:E.
    - unfold subtree_nat.
      destruct (decode j);auto.
    - assert (j > btsize (BT_node x0 b1 b2) - 1).
      + pose proof (sub_le_mono_r _ _ 1 H0) as T.
        simpl in H0. assert (j > j - 1) by nia. nia.
      + rewrite <- (encode_decode j) in H1.
        rewrite <- (encode_decode (btsize (BT_node _ _ _) -1)) in H1.
        apply nat_btidx_iff in H1. destruct H1.
        * eapply subtree_outrange_ltlen;eauto. exists x;auto.
        * eapply subtree_outrange_eqlen;eauto. exists x;auto.
  Qed.

  Lemma perfect_leaves (t : bintree A) :
    (exists n, perfect' t n) ->
    forall j, (btsize t - 1) / 2 <= j < btsize t ->
         match subtree_nat t j with
         | None => True
         | Some t' => leaf t'
         end.
  Proof.
    intros.
    unfold subtree_nat.
    remember (decode j) eqn:E. revert E H H0. revert l j.
    induction t;intros;destruct H.
    - destruct l;simpl;auto.
    - destruct l eqn:E1.
      + simpl. 
        pose proof (decode_nat j) as D.
        rewrite <- E in D. rewrite D in H0.
        assert ((btsize (BT_node x t1 t2) -1) /2 = 0) by nia.
        remember (div_small_iff (btsize (BT_node x t1 t2) -1) 2) as Y.
        assert (R : 2<>0) by nia;apply Y in R. clear HeqY. clear Y.
        apply R in H1. clear R. inversion H;subst.
        inversion H1.
        * rewrite  sub_0_r in H3. destruct (btsize t1) eqn:E1.
          ** simpl in H3. destruct t1;try (inversion E1).
             inversion H_l. rewrite <- H4 in H_r. inversion H_r;subst. auto.
          ** assert (btsize t2 = 0) by nia. destruct t2;try (inversion H2).
             inversion H_r. rewrite <- H5 in H_l. inversion H_l. auto.
        * inversion H3;subst.
          ** assert (btsize t1 = 0) by nia. assert (btsize t2 = 0) by nia.
             destruct t1;try (inversion H2). destruct t2;try (inversion H4). auto.
          ** inversion H5.
      + destruct d.
        * simpl. pose proof (decode_nat j) as D.
          rewrite <- E in D. eapply IHt1.
          ** apply (f_equal decode) in D. rewrite (decode_encode l0) in D.
             apply D.
          ** inversion H;subst. exists n;auto.
          ** simpl length. replace (S (length l0) -1) with (length l0) by nia.
             simpl btsize in H0. replace (S ( btsize t1 + btsize t2 ) -1) with ( btsize t1 + btsize t2 ) in H0 by nia.
             inversion H;subst. apply perf_size in H_l. apply perf_size in H_r.
             rewrite H_l in H0. rewrite H_r in H0. rewrite H_l.
             destruct H0. replace (S (2 ^ n - 1 + (2 ^ n - 1))) with (2^(S n)-1) in H1.
             2:{simpl. rewrite <- add_succ_l. rewrite Minus.minus_Sn_m.
                2:{ apply exp_pos. auto. } simpl. nia.
             } pose proof H1 as U. 
             replace ((2 ^ n - 1 + (2 ^ n - 1))/2) with (2^n - 1) in H0.
             2:{replace (2 ^ n - 1 + (2 ^ n - 1)) with ((2 ^ n - 1) * 2) by nia. 
                rewrite div_mul;nia. } pose proof H0 as R.
             apply decode_ubound in H1. rewrite <- E in H1. simpl in H1.
             apply Lt.lt_S_n in H1. unfold Peano.lt in H1.
             assert (length l0 <= n-1) by nia.
             apply decode_lbound in H0. rewrite <- E in H0. simpl in H0.
             assert (n-1 <= length l0) by nia.
             assert (n-1 = length l0) by nia.
             apply (f_equal (pow 2)) in H4. rewrite <- H4. 
             split. 
             *** replace ((2 ^ n - 1 - 1) / 2) with (2 ^ (n - 1)-1).
                 2:{destruct n. inversion H1. simpl pow.
                    replace (2 ^ n + (2 ^ n + 0) - 1 - 1) with ((2^n - 1) *2) by nia.
                    rewrite div_mul;auto. rewrite sub_0_r. auto. }
                 apply le_add_le_sub_l. replace (2 ^ (n - 1) + (2 ^ (n - 1) - 1)) with (2^n-1).
                 auto. rewrite add_sub_assoc. destruct n;inversion H1. simpl.
                 rewrite sub_0_r. nia. nia. apply exp_pos. auto.
             *** apply (f_equal encode) in E. rewrite (encode_unfold (Dir_left :: l0)) in E.
                 simpl in E. rewrite sub_0_r in E. rewrite (encode_decode j) in E.
                 assert (length l0 = n-1) by nia. apply encode_bound in H5. destruct H5.
                 replace (S(n-1)) with n in H6. 2:{destruct n. inversion H1. nia. }
                                              rewrite <- E. rewrite H4. rewrite add_sub. auto.
        * admit.                (* right half. similar to left one *)
  Admitted.

  Lemma complete_leaves (t : bintree A) :
    complete t ->
    forall j, j > btsize t / 2 ->
         match subtree_nat t (j - 1) with
         | None => True
         | Some t' => leaf t'
         end.
  Admitted.

  Lemma complete_fromList (xs : list A) : complete (fromList xs).
  Admitted.

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

  Lemma heap_erase_priority p t : heap_pr p t -> heap t.
  Proof. intros. destruct H; econstructor; assumption. Qed.

  Lemma heap_pr_if_heap (R_refl : forall x, R x x) t : btsize t >= 1 -> heap t -> exists p, heap_pr p t.
  Proof.
    intros Hₛ Hₕ.
    destruct Hₕ; simpl in Hₛ; try lia.
    eexists.
    econstructor; try assumption.
    eapply R_refl.
  Qed.

  Lemma heap_at_0 t : heap_at 0 t -> heap t.
  Proof.
    Local Transparent decode.
    unfold heap_at. simpl. tauto.
  Qed.

  Lemma heap_if_leaf t : leaf t -> heap t.
  Proof.
    intro H. destruct t.
    - econstructor.
    - simpl in H. destruct H. subst. econstructor; econstructor.
  Qed.

  Lemma heap_at_leaves t : complete t -> forall j, j > btsize t / 2 -> heap_at (j - 1) t.
  Proof.
    intros H j Hj. unfold heap_at.
    assert (H1 := complete_leaves t H j Hj).
    destruct (subtree_nat t (j-1)).
    - eapply heap_if_leaf; assumption.
    - auto.
  Qed.

  Lemma removelast_heap t : heap t -> heap (fromList (removelast (toList t))).
  Admitted.

End HeapProperty.

Section BinaryTreeZipper.

  Context {A : Type}.

  Inductive btctx : Type :=
  | btctx_top : btctx
  | btctx_left (x : A) (r : bintree A) (g : btctx) : btctx
  | btctx_right (x : A) (l : bintree A) (g : btctx) : btctx
  .

  Fixpoint recover_bintree (g : btctx) (t : bintree A) : bintree A :=
    match g with
    | btctx_top => t
    | btctx_left x r g => recover_bintree g (BT_node x t r)
    | btctx_right x l g => recover_bintree g (BT_node x l t)
    end.

End BinaryTreeZipper.

Arguments btctx : clear implicits.

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

Module NEO.

  Section BinaryTreeAccessories.

  Context {A : Type}.

  Definition toListAux root := map (fun i => @option_rect (bintree A) (fun _ => option A) option_root None (option_subtree (decode i) root)) (seq 0 ((2 ^ rank root) - 1)).

  Definition toList root := flat_map option2list (toListAux root).

  Definition insertInit (x : A) (t : bintree A) :=
    match t with
    | BT_nil => Some (BT_node x BT_nil BT_nil)
    | BT_node x l r => None
    end.

  Definition insertStep d acc t : option (bintree A) :=
    match t with
    | BT_nil => None
    | BT_node x l r =>
      match d with
      | Dir_left => option_map (fun l' => BT_node x l' r) (acc l)
      | Dir_right => option_map (fun r' => BT_node x l r') (acc r)
      end
    end.

  Definition insertAt (x : A) : list dir_t -> bintree A -> option (bintree A) := fold_right insertStep (insertInit x).

  Definition insertable (root : bintree A) i := subtree_nat root i = Some BT_nil.

  Definition fromListStep root := fun '(x, i) => @option_rect (bintree A) (fun _ => bintree A) id root (insertAt x (decode i) root).

  Definition fromList xs := fold_left fromListStep (add_indices xs) BT_nil.

  Definition isComplete root := Forall isSome (firstn (btsize root) (toListAux root)) /\ Forall isNone (skipn (btsize root) (toListAux root)).

  End BinaryTreeAccessories.

End NEO.
