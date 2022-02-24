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
Require Import HeapsortHeader.
Local Open Scope program_scope.

Section LList.

  Context {A : Type}.
  
  Lemma perfect2complete_list n (xss : list (list A)) :
    perfect_list n xss -> complete_list n xss.
  Proof.
    revert n. induction xss; simpl.
    - auto.
    - intros n [].
      left. split.
      + assumption.
      + eapply IHxss. assumption.
  Qed.

  Lemma splitLListRight_length' n (xss : list (list A)) :
    perfect_list (S n) xss ->
    length (splitLListRight n xss) = length xss.
  Proof.
    revert n.
    induction xss.
    - reflexivity.
    - intros. destruct H. simpl.
      rewrite H.
      pose_exp2 n.
      replace (2 ^ S n <=? 2 ^ n) with false by dec_nat.
      simpl.
      rewrite IHxss by assumption.
      reflexivity.
  Qed.

  Lemma complete_toLList n (xs : list A) : complete_list n (toLList n xs).
  Proof with lia || eauto.
    remember (length xs) as l.
    revert n xs Heql.
    induction l as [l IH] using Wf_nat.lt_wf_ind.
    intros n [ | x xs'].
    - intros Heql. now rewrite unfold_toLList.
    - set (xs := x :: xs'). intros Heql.
      rewrite unfold_toLList. unfold xs at 1. simpl.
      assert (claim1 : length (firstn (2^n) xs) = min (2^n) l).
      { rewrite Heql. apply firstn_length. }
      assert (claim2 : length (firstn (2 ^ n) xs) = 2 ^ n \/ length (firstn (2 ^ n) xs) < 2 ^ n) by lia.
      assert (claim3 : l > 0).
      { rewrite Heql. unfold xs. simpl... }
      pose_exp2 n.
      destruct claim2 as [claim2 | claim2]; [left | right].
      + split... eapply IH; try reflexivity. rewrite Heql.
        apply skipn_exp_length. simpl...
      + split...
        assert (claim5 : length (skipn (2 ^ n) xs) = 0).
        { rewrite skipn_length... }
        destruct (skipn (2 ^ n) xs)...
        inversion claim5.
  Qed.

  Lemma toLList_concat n (xss : list (list A)) :
    complete_list n xss ->
    toLList n (concat xss) = xss.
  Proof.
    revert n.
    induction xss as [| xs xss ].
    - auto.
    - intros.
      destruct H as [[H1 H2] | [H1 H2]].
      + rewrite unfold_toLList. simpl.
        pose_exp2 n.
        assert (xs <> []) by (intro; subst; simpl in *; lia).
        replace (null (xs ++ concat xss)) with false by dec_list.
        rewrite firstn_exact, skipn_exact by auto.
        rewrite IHxss by assumption.
        reflexivity.
      + subst. rewrite unfold_toLList. simpl. rewrite app_nil_r.
        replace (null xs) with false by (dec_list; subst; simpl in *; lia).
        rewrite firstn_all2 by lia.
        rewrite skipn_all2 by lia.
        reflexivity.
  Qed.

  Lemma perfect_zipLList n (xss yss : list (list A)) :
    perfect_list n xss ->
    perfect_list n yss ->
    length xss = length yss ->
    perfect_list (S n) (zipLList xss yss).
  Proof.
    revert n yss.
    induction xss as [| xs xss ]; intros;
    destruct yss as [| ys yss ]; try discriminate.
    - simpl. auto.
    - simpl in *. destruct H, H0. split.
      + rewrite app_length. lia.
      + eapply IHxss.
        * assumption.
        * assumption.
        * auto.
  Qed.

  Lemma complete_zipLList n (xss yss : list (list A)) :
    perfect_list n xss /\ complete_list n yss /\ length xss = length yss \/
    complete_list n xss /\ perfect_list n yss /\ length xss = S (length yss) ->
    complete_list (S n) (zipLList xss yss).
  Proof.
    revert n yss.
    induction xss as [| xs xss ]; intros; destruct yss as [| ys yss ].
    - simpl. auto.
    - destruct H as [[H1 [H2 H3]] | [H1 [H2 H3]]]; discriminate.
    - destruct H as [[H1 [H2 H3]] | [H1 [H2 H3]]].
      + discriminate.
      + simpl in *.
        right.
        split.
        * pose_exp2 n. lia.
        * destruct xss; try discriminate.
          reflexivity.
    - destruct H as [[H1 [H2 H3]] | [H1 [H2 H3]]].
      + simpl in *.
        destruct H2.
        * left. split.
          -- rewrite app_length. lia.
          -- eapply IHxss. left.
             destruct H1, H. auto.
        * right. split.
          -- rewrite app_length. lia.
          -- destruct H. subst.
             destruct xss; try discriminate.
             reflexivity.
      +  simpl in *.
         destruct H1.
         * left. split.
           -- rewrite app_length. lia.
           -- eapply IHxss. right.
              destruct H, H2. auto.
         * destruct H; subst.
           discriminate.
  Qed.

  Lemma splitLeft_zip n (xss yss : list (list A)) :
    perfect_list n xss /\ complete_list n yss /\ length xss = length yss \/
    complete_list n xss /\ perfect_list n yss /\ length xss = 1 + length yss ->
    splitLListLeft n (zipLList xss yss) = xss.
  Proof.
    revert n yss.
    induction xss as [| xs xss ]; intros; destruct yss as [| ys yss ].
    - reflexivity.
    - destruct H as [[H1 [H2 H3]] | [H1 [H2 H3]]]; discriminate.
    - destruct H as [[H1 [H2 H3]] | [H1 [H2 H3]]]; try discriminate.
      destruct xss; try discriminate.
      simpl in *.
      rewrite firstn_all2 by lia.
      reflexivity.
    - destruct H as [[H1 [H2 H3]] | [H1 [H2 H3]]].
      + simpl in *.
        rewrite firstn_exact by lia.
        destruct H2.
        * destruct H1, H.
          rewrite IHxss by auto.
          reflexivity.
        * destruct H. subst.
          destruct xss; try discriminate.
          reflexivity.
      + simpl in *.
        destruct H1 as [[H1 H4] | [H1 H4]]; subst; try discriminate.
        rewrite firstn_exact by lia.
        destruct H2.
        rewrite IHxss by auto.
        reflexivity.
  Qed.

  Lemma splitRight_zip n (xss yss : list (list A)) :
    perfect_list n xss /\ complete_list n yss /\ length xss = length yss \/
    complete_list n xss /\ perfect_list n yss /\ length xss = 1 + length yss ->
    splitLListRight n (zipLList xss yss) = yss.
  Proof.
    revert n yss.
    induction xss as [| xs xss ]; intros; destruct yss as [| ys yss ].
    - reflexivity.
    - destruct H as [[H1 [H2 H3]] | [H1 [H2 H3]]]; discriminate.
    - destruct H as [[H1 [H2 H3]] | [H1 [H2 H3]]]; try discriminate.
      simpl in *.
      rewrite leb_correct by lia.
      reflexivity.
    - simpl in *.
      rewrite app_length.
      pose_exp2 n.
      rewrite leb_correct_conv by lia.
      destruct H as [[H1 [H2 H3]] | [H1 [H2 H3]]].
      + destruct H1.
        rewrite skipn_exact by auto.
        destruct H2 as [[H2 H4] | [H2 H4]].
        * rewrite IHxss by auto.
          reflexivity.
        * subst.
          destruct xss; try discriminate.
          reflexivity.
      + destruct H1.
        * rewrite skipn_exact by lia.
          destruct H, H2.
          rewrite IHxss by auto.
          reflexivity.
        * destruct H. subst. discriminate.
  Qed.

  Lemma zip_split n (xss : list (list A)) : complete_list (S n) xss -> zipLList (splitLListLeft n xss) (splitLListRight n xss) = xss.
    revert n.
    induction xss as [| xs xss ].
    - reflexivity.
    - intros.
      Opaque pow.
      simpl in H.
      Transparent pow.
      destruct H; destruct H.
      + simpl in *.
        pose_exp2 n.
        replace (length xs <=? 2 ^ n) with false by dec_nat.
        rewrite firstn_skipn.
        rewrite IHxss by assumption.
        reflexivity.
      + subst. simpl.
        destruct (length xs <=? 2^n) eqn: E.
        * rewrite firstn_all2.
          reflexivity.
          eapply leb_complete.
          auto.
        * rewrite firstn_skipn.
          reflexivity.
  Qed.

  Lemma perfect_splitLListLeft n (xss : list (list A)) :
    perfect_list (S n) xss ->
    perfect_list n (splitLListLeft n xss).
  Proof.
    revert n. induction xss; intros.
    - simpl. auto.
    - destruct H. split.
      + eapply firstn_length_le.
        rewrite H.
        pose_exp2 n.
        simpl; lia.
      + eapply IHxss. assumption.
  Qed.

  Lemma perfect_splitLListRight n (xss : list (list A)) :
    perfect_list (S n) xss ->
    perfect_list n (splitLListRight n xss).
  Proof.
    revert n. induction xss; intros.
    - simpl. auto.
    - destruct H. simpl.
      rewrite H.
      pose_exp2 n.
      replace (2 ^ S n <=? 2 ^ n) with false by dec_nat.
      split.
      + rewrite skipn_length. rewrite H. simpl; lia.
      + eapply IHxss. assumption.
  Qed.

  Lemma complete_splitLList n (xss : list (list A)) :
    complete_list (S n) xss ->
    let d := length xss in
    let l := splitLListLeft n xss in
    let r := splitLListRight n xss in
    perfect_list n l /\ length l = d /\ complete_list n r /\ length r = d \/
    complete_list n l /\ length l = d /\ perfect_list n r /\ exists d', length r = d' /\ d' + 1 = d.
  Proof.
    revert n.
    induction xss as [| xs xss ].
    - intros.
      simpl in d, l, r.
      subst d l r.
      auto.
    - intros.
      simpl in H.
      destruct H as [[]|[]].
      + pose_exp2 n. rename H1 into Hn.
        assert (Hl : length xs > 2 ^ n) by lia.
        pose proof (IHxss (S n) H0).
        simpl in d, l, r.
        remember (length xss) as d'.
        remember (splitLListLeft (S n) xss) as l'.
        remember (splitLListRight (S n) xss) as r'.
        simpl in H1.
        destruct H1 as [[H1 [H2 [H3 H4]]] | [H1 [H2 [H3 H4]]]].
        * left. subst d l r.
          replace (length xs <=? 2 ^ n) with false
            by (symmetry; eapply leb_correct_conv; lia).
          split; [| split; [| split ]].
          -- simpl.
             rewrite firstn_length_le by lia.
             auto.
          -- simpl. auto.
          -- simpl. left.
             rewrite skipn_length. rewrite H. simpl. split; try lia; auto.
          -- simpl. auto.
        * right. subst d l r.
          replace (length xs <=? 2 ^ n) with false
            by (symmetry; eapply leb_correct_conv; lia).
          split; [| split; [| split ]].
          -- simpl. left.
             rewrite firstn_length_le by lia.
             auto.
          -- simpl. auto.
          -- simpl. rewrite skipn_length. rewrite H. simpl. split; try lia; auto.
          -- destruct H4 as [d [H4 H5]].
             exists (S d). simpl.
             split; lia.
      + subst xss.
        simpl in d, l, r.
        destruct (length xs <=? 2 ^ n) eqn:E.
        * eapply leb_complete in E.
          right. subst d l r.
          split; [| split; [| split ]].
          -- simpl.
             rewrite firstn_all2 by assumption.
             assert (length xs = 2 ^ n \/ length xs <> 2 ^ n) by lia.
             destruct H0.
             ++ left. auto.
             ++ right. split; [lia | reflexivity].
          -- reflexivity.
          -- simpl. auto.
          -- exists 0. auto.
        * eapply leb_complete_conv in E.
          left. subst d l r.
          split; [| split; [| split ]].
          -- simpl.
             rewrite firstn_length. lia.
          -- reflexivity.
          -- simpl. right.
             rewrite skipn_length.
             simpl in H.
             split; [ lia | reflexivity ].
          -- reflexivity.
  Qed.

  Lemma complete_splitLListLeft n (xss : list (list A)) : complete_list (S n) xss -> complete_list n (splitLListLeft n xss).
  Proof.
    intros H.
    destruct (complete_splitLList n xss H) as [[H1 [H2 [H3 H4]]] | [H1 [H2 [H3 H4]]]].
    - eapply perfect2complete_list. assumption.
    - assumption.
  Qed.

  Lemma complete_splitLListRight n (xss : list (list A)) : complete_list (S n) xss -> complete_list n (splitLListRight n xss).
  Proof.
    intros H.
    destruct (complete_splitLList n xss H) as [[H1 [H2 [H3 H4]]] | [H1 [H2 [H3 H4]]]].
    - assumption.
    - eapply perfect2complete_list. assumption.
  Qed.

  Lemma In_zipLList (x : A) xss yss :
    In x (concat (zipLList xss yss)) ->
    In x (concat xss) \/ In x (concat yss).
  Proof.
    revert yss. induction xss as [| xs xss ]; [| destruct yss as [| ys yss ] ]; auto.
    intros. simpl in H.
    eapply in_app_or in H. destruct H.
    - eapply in_app_or in H. destruct H.
      + left. simpl. eapply in_or_app. auto.
      + right. simpl. eapply in_or_app. auto.
    - eapply IHxss in H. destruct H.
      + left. simpl. eapply in_or_app. auto.
      + right. simpl. eapply in_or_app. auto.
  Qed.

  Lemma splitLListLeft_toLList_concat n xss (y : A) :
    complete_list (S n) xss ->
    splitLListLeft n (toLList (S n) (concat xss ++ [y])) = toLList n (concat (splitLListLeft n xss) ++ [y]) \/
    splitLListLeft n (toLList (S n) (concat xss ++ [y])) = (splitLListLeft n xss).
  Proof.
    revert n.
    induction xss as [| xs xss ].
    - intros. simpl. left.
      pose_exp2 n.
      repeat (
          simpl;
          repeat first
            [ rewrite (firstn_all2 [y]) by (simpl; lia)
            | rewrite (skipn_all2 [y]) by (simpl; lia)
            ];
          rewrite unfold_toLList
        ).
      reflexivity.
    - intros. simpl in H.
      destruct H as [[H1 H2] | [H1 H2]].
      + destruct (IHxss _ H2).
        * left. simpl.
          (* TODO : make lemma for unfolding toLList *)
          rewrite unfold_toLList.
          replace (null _) with false by dec_list.
          rewrite <- app_assoc.
          rewrite firstn_exact, skipn_exact by auto.
          rewrite (unfold_toLList n).
          replace (null _) with false by dec_list.
          rewrite <- app_assoc.
          rewrite firstn_exact, skipn_exact by (rewrite firstn_length; lia).
          simpl.
          rewrite H.
          reflexivity.
        * right. simpl.
          rewrite unfold_toLList.
          replace (null _) with false by dec_list.
          rewrite <- app_assoc.
          rewrite firstn_exact, skipn_exact by (simpl; lia).
          simpl.
          rewrite H.
          reflexivity.
      + subst. simpl. rewrite 2 app_nil_r.
        rewrite unfold_toLList.
        replace (null _) with false by dec_list.
        rewrite firstn_all2 by (rewrite app_length; simpl; lia).
        rewrite skipn_all2 by (rewrite app_length; simpl; lia).
        rewrite unfold_toLList.
        simpl.
        assert (length xs < 2 ^ n \/ length xs >= 2 ^ n) by lia.
        destruct H.
        * left.
          rewrite firstn_all2 by (rewrite app_length; simpl; lia).
          rewrite firstn_all2 by lia.
          rewrite unfold_toLList.
          replace (null _) with false by dec_list.
          rewrite firstn_all2 by (rewrite app_length; simpl; lia).
          rewrite skipn_all2 by (rewrite app_length; simpl; lia).
          reflexivity.
        * right.
          rewrite firstn_app.
          replace (2 ^ n - length xs) with 0 by lia.
          simpl. rewrite app_nil_r.
          reflexivity.
  Qed.

  Lemma splitLListRight_toLList_concat n xss (y : A) :
    complete_list (S n) xss ->
    splitLListRight n (toLList (S n) (concat xss ++ [y])) = toLList n (concat (splitLListRight n xss) ++ [y]) \/
    splitLListRight n (toLList (S n) (concat xss ++ [y])) = (splitLListRight n xss).
  Proof.
    revert n. induction xss as [| xs xss ].
    - intros. simpl. right.
      pose_exp2 n.
      rewrite unfold_toLList.
      replace (null _) with false by reflexivity.
      rewrite (firstn_all2 [y]) by (simpl; lia).
      rewrite (skipn_all2 [y]) by (simpl; lia).
      rewrite unfold_toLList.
      replace (null _) with true by reflexivity.
      unfold splitLListRight.
      simpl length.
      replace (1 <=? 2 ^ n) with true by dec_nat.
      reflexivity.
    - intros. simpl in H.
      destruct H as [[H1 H2] | [H1 H2]].
      + destruct (IHxss _ H2).
        * left. simpl.
          pose_exp2 n.
          replace (length xs <=? 2 ^ n) with false by dec_nat.
          simpl.
          rewrite unfold_toLList.
          replace (null _) with false by dec_list.
          rewrite <- app_assoc.
          rewrite firstn_exact, skipn_exact by (simpl; lia).
          simpl.
          replace (length xs <=? 2 ^ n) with false by dec_nat.
          rewrite (unfold_toLList n).
          replace (null _) with false by dec_list.
          rewrite <- app_assoc.
          rewrite firstn_exact, skipn_exact by (rewrite skipn_length; lia).
          rewrite H.
          reflexivity.
        * right. simpl.
          pose_exp2 n.
          replace (length xs <=? 2 ^ n) with false by dec_nat.
          rewrite unfold_toLList.
          replace (null _) with false by dec_list.
          rewrite <- app_assoc.
          rewrite firstn_exact, skipn_exact by (simpl; lia).
          simpl.
          replace (length xs <=? 2 ^ n) with false by dec_nat.
          rewrite H.
          reflexivity.
      + subst. simpl concat at 1 3. rewrite app_nil_r.
        assert (length xs < 2 ^ n \/ length xs = 2 ^ n \/ length xs > 2 ^ n) by lia.
        destruct H.
        * right.
          rewrite unfold_toLList.
          replace (null _) with false by dec_list.
          rewrite firstn_all2 by (rewrite app_length; simpl; lia).
          rewrite skipn_all2 by (rewrite app_length; simpl; lia).
          rewrite unfold_toLList.
          simpl.
          replace (length xs <=? 2 ^ n) with true by dec_nat.
          replace (length (xs ++ [y]) <=? 2 ^ n) with true by (rewrite app_length; dec_nat).
          reflexivity.
        * left.
          replace (concat (splitLListRight n [xs])) with (skipn (2 ^ n) xs).
          2: { simpl. destruct H.
               - replace (length xs <=? 2 ^ n) with true by dec_nat.
                 rewrite <- H.
                 rewrite skipn_all.
                 reflexivity.
               - replace (length xs <=? 2 ^ n) with false by dec_nat.
                 simpl.
                 rewrite app_nil_r.
                 reflexivity.
          }
          rewrite unfold_toLList.
          replace (null _) with false by dec_list.
          rewrite firstn_all2 by (rewrite app_length; simpl; lia).
          rewrite skipn_all2 by (rewrite app_length; simpl; lia).
          rewrite unfold_toLList.
          replace (null _) with true by reflexivity.
          rewrite unfold_toLList.
          replace (null _) with false by dec_list.
          rewrite firstn_all2 by (rewrite app_length, skipn_length; simpl; lia).
          rewrite (skipn_all2 (skipn (2 ^ n) xs ++ [y])) by (rewrite app_length, skipn_length; simpl; lia).
          rewrite unfold_toLList.
          simpl.
          replace (length (xs ++ [y]) <=? 2 ^ n) with false by (rewrite app_length; dec_nat).
          rewrite skipn_app.
          replace (2 ^ n - length xs) with 0 by lia.
          reflexivity.
  Qed.

  Lemma zipLList_permutation (xss yss : list (list A)) : Permutation (concat (zipLList xss yss)) (concat xss ++ concat yss).
  Proof.
    revert yss.
    induction xss as [| xs xss ].
    - reflexivity.
    - intros.
      destruct yss as [| ys yss ].
      + simpl. rewrite app_nil_r. reflexivity.
      + simpl. rewrite IHxss.
        rewrite 2 app_assoc.
        eapply Permutation_app_tail.
        rewrite <- 2 app_assoc.
        rewrite (Permutation_app_comm ys (concat xss)).
        reflexivity.
  Qed.

End LList.

Section BinaryTreeIndexing.

  Lemma unfold_decode i :
    decodeIdx i =
    if Nat.eq_dec i 0 then [] else
    if Nat.eq_dec (i mod 2) 1
    then decodeIdx ((i - 1) / 2) ++ [Dir_left]
    else decodeIdx ((i - 2) / 2) ++ [Dir_right].
  Proof with lia || discriminate || eauto.
    apply encode_inj. rewrite encode_decode.
    destruct (Nat.eq_dec i 0) as [H_yes1 | H_no1]...
    assert (claim1 := Nat.mod_bound_pos i 2).
    destruct (Nat.eq_dec (i mod 2) 1) as [H_yes2 | H_no2];
      [assert (claim2 := encode_decode ((i - 1) / 2)) | assert (claim2 := encode_decode ((i - 2) / 2))].
    all: symmetry; revert claim2; unfold encodeIdx; intros H_eq;
      rewrite fold_left_last; unfold dir_t_rect at 1;
      rewrite H_eq; symmetry.
    - apply positive_odd...
    - apply positive_even...
  Qed.

  Lemma decode_nat n :
    match decodeIdx n with
    | [] => n = 0
    | Dir_left :: l => encodeIdx l = n - 2 ^ (length (decodeIdx n)-1)
    | Dir_right :: l => encodeIdx l = n - 2 ^ (length (decodeIdx n))
    end.
  Proof with auto.
    destruct (decodeIdx n) eqn:E.
    - apply (f_equal encodeIdx) in E;rewrite (encode_decode n) in E.
      unfold encodeIdx in E; simpl in E...
    - apply (f_equal encodeIdx) in E;rewrite (encode_decode n) in E;rewrite E.
      rewrite (encode_unfold (d :: l)). destruct d;simpl;nia.
  Qed.

  Lemma encode_bound l n : length l = n -> 2^n -1 <= encodeIdx l < 2 ^ (S n) -1.
  Proof.
    revert n. induction l;intros.
    - simpl in *. rewrite <- H. simpl. auto.
    - simpl in *. destruct n;inversion H.
      rewrite encode_unfold. destruct a.
      + simpl. rewrite H1. apply IHl in H1. rewrite sub_0_r.
        pose_exp2 n. lia.
      + simpl. rewrite H1. apply IHl in H1.
        pose_exp2 n. lia.
  Qed.
  
  Lemma decode_ubound j n : j < 2 ^ n - 1 -> length (decodeIdx j) < n.
  Proof.
    intros. pose proof (lt_dec (length (decodeIdx j)) n) as Y.
    destruct Y;auto.
    assert (length (decodeIdx j) >= n) by nia.
    remember (length (decodeIdx j)) as m.
    symmetry in Heqm. apply encode_bound in Heqm.
    rewrite encode_decode in Heqm.
    assert (2 ^ n <= 2 ^ m) by now apply pow_le_mono_r.
    nia.
  Qed.

  Lemma decode_lbound j n : 2 ^ n -1 <= j -> n <= length (decodeIdx j).
  Proof.
    intros. pose proof (lt_dec n (S (length (decodeIdx j)))) as Y.
    destruct Y; try nia.
    assert (S (length (decodeIdx j)) <= n) by nia.
    remember (length (decodeIdx j)) as m.
    symmetry in Heqm. apply encode_bound in Heqm.
    rewrite encode_decode in Heqm.
    assert (2 ^ S m <= 2 ^ n) by now apply pow_le_mono_r.
    nia.
  Qed.

  Lemma encode_lt_eqlen d i j : length i = length j -> encodeIdx (d :: i) < encodeIdx (d :: j) -> encodeIdx i < encodeIdx j.
  Proof.
    intro H.
    rewrite (encode_unfold (d :: i)).
    rewrite (encode_unfold (d :: j)).
    simpl length. rewrite H.
    destruct d; lia.
  Qed.

  Lemma btidx_lt_complete i j : encodeIdx i < encodeIdx j -> btidx_lt i j.
  Proof.
    assert (length i < length j \/ length i = length j \/ length i > length j) by lia.
    destruct H as [|[]].
    - unfold btidx_lt. left. assumption.
    - intros H1. right.
      revert j H H1.
      induction i as [|x i].
      + intros. destruct j; simpl in H; try lia.
      + intros. destruct j as [|y j]; simpl in H; try lia.
        eapply succ_inj in H.
        destruct x, y.
        * econstructor. eapply IHi.
          -- assumption.
          -- eapply encode_lt_eqlen; eassumption.
        * econstructor. assumption.
        * exfalso.
          rewrite (encode_unfold (Dir_right :: i)) in H1.
          rewrite (encode_unfold (Dir_left :: j)) in H1.
          simpl length in H1.
          rewrite <- H in H1.
          remember (length i) as n.
          assert (2 ^ n - 1 <= encodeIdx i < 2 ^ S n - 1) by (eapply encode_bound; auto).
          assert (2 ^ n - 1 <= encodeIdx j < 2 ^ S n - 1) by (eapply encode_bound; auto).
          simpl pow in *. rewrite sub_0_r in H1. lia.
        * econstructor. eapply IHi.
          -- assumption.
          -- eapply encode_lt_eqlen; eassumption.
    - intros H'. exfalso.
      remember (length i) as m.
      remember (length j) as n.
      assert (2 ^ m - 1 <= encodeIdx i < 2 ^ S m - 1) by (eapply encode_bound; auto).
      assert (2 ^ n - 1 <= encodeIdx j < 2 ^ S n - 1) by (eapply encode_bound; auto).
      assert (2 ^ S n <= 2 ^ m) by (eapply pow_le_mono_r; lia).
      lia.
  Qed.

End BinaryTreeIndexing.

Section BinaryTreeAccessories.

  Context {A : Type}.

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
    forall (root : bintree A),
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
    enough (claim1 : @option_subtree A (ds ++ [d]) = fold_right subtree_step (subtree_step d subtree_init) ds).
    - rewrite claim1. clear claim1. unfold option_subtree. induction ds; destruct d; destruct root; eauto.
    - unfold option_subtree at 1. rewrite <- rev_involutive with (l := ds ++ [d]) at 1.
      rewrite fold_left_rev_right, rev_unit. simpl. now rewrite <- fold_left_rev_right, rev_involutive.
  Qed.

  Lemma option_subtree_last' i (t : bintree A) :
    match option_subtree i t with
    | Some (BT_node x l r) =>
      option_subtree (i ++ [Dir_left]) t = Some l /\
      option_subtree (i ++ [Dir_right]) t = Some r
    | _ => True
    end.
  Proof.
    assert (H1 := option_subtree_last i Dir_left t).
    assert (H2 := option_subtree_last i Dir_right t).
    destruct (option_subtree i t) as [ [] |]; auto.
  Qed.

  Lemma toListAux_fromListAux (xss : list (list A)) : complete_list 0 xss -> toListAux (fromListAux xss) = xss.
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
        erewrite IH with (xss := splitLListLeft 0 xss); try reflexivity.
        erewrite IH with (xss := splitLListRight 0 xss); try reflexivity.
        rewrite zip_split by assumption.
        reflexivity.
        * assert (length (splitLListRight 0 xss) <= length xss)
            by eapply splitLListRight_length.
          simpl. lia.
        * eapply complete_splitLListRight; assumption.
        * rewrite splitLListLeft_length. simpl. lia.
        * eapply complete_splitLListLeft; assumption.
  Qed.

  Lemma toList_fromList (xs : list A) : toList (fromList xs) = xs.
  Proof.
    unfold fromList, toList.
    rewrite toListAux_fromListAux by eapply complete_toLList.
    eapply concat_toLList.
  Qed.

  Lemma toList_length (t : bintree A) : length (toList t) = btsize t.
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

  Lemma toList_step (t : bintree A) : btsize t >= 1 -> match t with
                                       | BT_nil => False
                                       | BT_node x _ _ => toList t = x :: tail (toList t)
                                       end.
  Proof.
    intros.
    destruct t; simpl in H; try lia.
    reflexivity.
  Qed.

  Lemma toList_permutation (x : A) l r : Permutation (toList (BT_node x l r)) ([x] ++ (toList l) ++ (toList r)).
  Proof.
    unfold toList. simpl.
    rewrite zipLList_permutation.
    reflexivity.
  Qed.

  Lemma toList_btin (x : A) t : In x (toList t) -> btin x t.
  Proof.
    induction t.
    - simpl. contradiction.
    - simpl.
      intros.
      destruct H.
      + subst. econstructor.
      + assert (In x (toList t1) \/ In x (toList t2))
          by (apply In_zipLList; assumption).
        destruct H0.
        * eapply btin_left.
          eapply IHt1.
          assumption.
        * eapply btin_right.
          eapply IHt2.
          assumption.
  Qed.

  Lemma btpartial_fromListAux (xss : list (list A)) (y : A) :
    complete_list 0 xss ->
    btpartial (fromList (concat xss ++ [y])) (fromListAux xss).
  Proof.
    unfold fromList.
    remember (length xss) as n.
    revert xss Heqn.
    induction n as [n IH] using Wf_nat.lt_wf_ind. intros.
    destruct n.
    - destruct xss; try discriminate.
      vm_compute. econstructor.
    - destruct xss as [| xs xss ]; try discriminate.
      rewrite unfold_toLList.
      replace (null _) with false by dec_list.
      simpl in H, Heqn.
      destruct H as [[H1 H2] | [H1 H2]]; try lia.
      destruct xs as [| x []]; try discriminate. simpl.
      rewrite unfold_fromListAux.
      rewrite (unfold_fromListAux ([x] :: xss)).
      econstructor.
      + destruct (splitLListLeft_toLList_concat 0 xss y H2).
        * rewrite H.
          eapply (IH n).
          -- lia.
          -- rewrite splitLListLeft_length. lia.
          -- eapply complete_splitLListLeft. assumption.
        * rewrite H. eapply btpartial_refl.
      + destruct (splitLListRight_toLList_concat 0 xss y H2).
        * rewrite H.
          eapply IH.
          2: reflexivity.
          -- pose proof (splitLListRight_length 0 xss). lia.
          -- eapply complete_splitLListRight. assumption.
        * rewrite H.
          eapply btpartial_refl.
  Qed.

  Lemma btpartial_fromList (xs : list A) y :
    btpartial (fromList (xs ++ [y])) (fromList xs).
  Proof.
    unfold fromList.
    remember (toLList 0 xs) as xss.
    assert (xs = concat xss) by (subst; rewrite concat_toLList; reflexivity).
    rewrite H.
    eapply btpartial_fromListAux.
    subst.
    eapply complete_toLList.
  Qed.

End BinaryTreeAccessories.

Section CompleteBinaryTree.

  Context {A : Type}.

  Lemma perfect'2complete' {n} (t : bintree A)
    (H_perfect : perfect' t n)
    : complete' t n.
  Proof.
    induction H_perfect as [ | n x l r H_l IH_l H_r IH_r].
    - exact (complete_nil).
    - exact (complete_node_perfect_complete x l r H_l IH_r).
  Qed.

  Lemma destruct_complete (t : bintree A) (H_complete : complete t) :
    match t with
    | BT_nil => True
    | BT_node x l r => complete l /\ complete r
    end.
  Proof with eauto.
    pose proof (perfect_coerce_complete := @perfect'2complete'). destruct H_complete as [t_rk H_complete'].
    destruct t as [ | x l r]... inversion H_complete'; subst; split; eexists...
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

  Lemma perf_size (t : bintree A) n :
    perfect' t n ->
    btsize t = 2 ^ n -1.
  Proof.
    intros. induction H;auto.
    simpl. rewrite IHperfect'1. rewrite IHperfect'2.
    pose_exp2 n. lia.
  Qed.

  Lemma comp_size (t : bintree A) n :
    complete' t (S n) ->
    2 ^ n <= btsize t <= 2 ^ (S n) - 1.
  Proof.
    revert t. induction n;intros.
    - inversion H;subst. simpl. inversion H_l;subst. inversion H_r;subst. simpl. auto.
    - inversion H;subst.
      + apply perf_size in H_l. simpl. rewrite H_l.
        rewrite <- add_succ_l. pose_exp2 n.
        replace (S (2 ^ n -1)) with (2 ^ n) by nia.
        assert (btsize r <= 2 ^ S n - 1).
        * clear IHn H0 H_l H l x.
          admit. (*
          induction H_r using complete_ind_ranked. simpl.
          ** pose_exp2 n. lia.
          ** destruct H;subst.
             *** simpl in *. pose_exp2 n_l. lia.
             *** simpl in *. pose_exp2 n_r. lia.
             *)
        * simpl in *. nia.
      + apply perf_size in H_r. simpl. rewrite H_r.
        rewrite <- add_succ_r.
        apply IHn in H_l.
        pose_exp2 n.
        replace (S (2 ^ n - 1)) with (2 ^ n) by nia.
        simpl in *. nia.
  Admitted.

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

  Lemma perfect'_rank (t : bintree A) n
    (H_perfect : perfect' t n)
    : rank t = n.
  Proof. induction H_perfect; simpl; lia. Qed.

  Lemma complete'_rank (t : bintree A) n
    (H_complete : complete' t n)
    : rank t = n.
  Proof. induction H_complete. 2: apply perfect'_rank in H_l. 3: apply perfect'_rank in H_r. all: simpl; lia. Qed.

  Lemma last_btidx_nil : last_btidx (BT_nil : bintree A) = [].
  Proof. reflexivity. Qed.

  Lemma btidx_lt_mono i j x y :
    btidx_lt i j -> btidx_lt (i ++ [x]) (j ++ [y]).
  Proof.
    intros H.
    destruct H.
    - left. unfold lt_ltlen in *.
      rewrite 2 app_length. simpl. lia.
    - right.
      induction H.
      + simpl. econstructor. rewrite 2 app_length. simpl. lia.
      + simpl. econstructor. assumption.
  Qed.

  Lemma last_btidx_half (t : bintree A) j d :
    btidx_lt (removelast (last_btidx t)) j ->
    btidx_lt (last_btidx t) (j ++ [d]).
  Proof.
    intros H.
    remember (last_btidx t) as i; clear Heqi.
    assert (Hnil : i = [] \/ i <> []) by (destruct i; [ left; reflexivity | right; congruence ]).
    destruct Hnil.
    - subst i. left. unfold lt_ltlen.
      rewrite app_length.
      simpl. lia.
    - rewrite (app_removelast_last Dir_left H0).
      eapply btidx_lt_mono.
      assumption.
  Qed.

  Lemma last_btidx_perfect_complete (x : A) l r n :
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
        2: { simpl. pose_exp2 n. lia. }
        replace (S (2 ^ S n - 1) - 1) with (2 ^ S n - 1) in H2 by nia. auto.
      + apply decode_ubound in H3. assert (length (decode (btsize r - 1)) = n) by nia.
        rewrite H4. simpl. pose_exp2 n. lia.
  Qed.
    
  Lemma last_btidx_complete_perfect (x : A) l r n :
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
    pose_exp2 n.
    assert (2 ^ S n >= 2) by (simpl;nia).
    assert (btsize l - 1 < 2 ^ S n - 1) by nia.
    apply decode_ubound in H4. assert (length (decode (btsize l -1)) = n) by nia.
    rewrite H5. simpl. rewrite sub_0_r. nia.
  Qed.

  Lemma complete'_last_btidx_length (t : bintree A) n :
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
  Proof with first [ lia | eassumption | eapply perfect'2complete'; eassumption | idtac ].
    unfold lt_ltlen.
    intros [n H] j Hj.
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
      erewrite last_btidx_perfect_complete with (n := S n) in Hj...
      destruct j as [|[] j]; simpl in Hj...
      + rewrite unfold_option_subtree; simpl.
        erewrite complete'_last_btidx_length in Hj...
        eapply (IH (S n))...
        erewrite complete'_last_btidx_length...
        lia.
      + rewrite unfold_option_subtree; simpl.
        eapply (IH (S n))...
    - erewrite last_btidx_complete_perfect in Hj...
      destruct j as [|[] j]; simpl in Hj...
      + rewrite unfold_option_subtree; simpl.
        eapply (IH (S n))...
      + rewrite unfold_option_subtree; simpl.
        erewrite complete'_last_btidx_length in Hj...
        eapply (IH n)...
        erewrite complete'_last_btidx_length...
        lia.
  Qed.

  (* It's possible to prove option_subtree j t = Some BT_nil *)
  Lemma subtree_outrange_eqlen (t : bintree A) :
    complete t ->
    forall j, lt_eqlen (last_btidx t) j ->
         option_subtree j t = Some BT_nil \/ option_subtree j t = None.
  Proof with first [ lia | eassumption | eapply perfect'2complete'; eassumption | idtac ].
    intros [n H] j Hj.
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
      erewrite last_btidx_perfect_complete with (n := S n) in Hj...
      inversion Hj; subst.
      rewrite unfold_option_subtree; simpl.
      eapply (IH (S n))...
    - erewrite last_btidx_complete_perfect in Hj...
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
        * eexists...
        * unfold lt_ltlen.
          rewrite <- H1.
          erewrite 2 complete'_last_btidx_length...
          lia.
      + rewrite unfold_option_subtree; simpl.
        eapply (IH (S n))...
  Qed.

  Lemma subtree_outrange (t : bintree A) :
    complete t ->
    forall j, btidx_lt (last_btidx t) j ->
         option_subtree j t = Some BT_nil \/ option_subtree j t = None.
  Proof.
    intros H j Hj.
    destruct Hj.
    - eapply subtree_outrange_ltlen; assumption.
    - eapply subtree_outrange_eqlen; assumption.
  Qed.

  Lemma subtree_leaf (t : bintree A) :
    complete t ->
    forall j, btidx_lt (removelast (last_btidx t)) j ->
         match option_subtree j t with
         | Some t' => leaf t'
         | None => True
         end.
  Proof.
    intros H j Hj.
    assert (H1 := option_subtree_last' j t).
    assert (Hlt : forall d, btidx_lt (last_btidx t) (j ++ [d])) by (intros; eapply last_btidx_half; eassumption).
    destruct (option_subtree j t) as [[]|].
    - auto.
    - destruct H1 as [Hl Hr]. split.
      + destruct (subtree_outrange t H _ (Hlt Dir_left)) as [H2|H2];
          rewrite H2 in Hl; inversion Hl.
        reflexivity.
      + destruct (subtree_outrange t H _ (Hlt Dir_right)) as [H2|H2];
          rewrite H2 in Hr; inversion Hr.
        reflexivity.
    - auto.
  Qed.

  (*
  Lemma subtree_nat_outrange j (t : bintree A) :
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
   *)

  Lemma encode_removelast j : encode (removelast j) = (encode j + 1) / 2 - 1.
  Proof.
    assert (j = [] \/ j <> [])
      by (destruct j; [ left; reflexivity | right; congruence]).
    destruct H.
    - subst j. reflexivity.
    - rewrite (app_removelast_last Dir_left H) at 2.
      rewrite encode_last.
      remember (encode (removelast j)) as n.
      destruct (last j Dir_left).
      + replace (2 * n + 1 + 1) with ((n + 1) * 2) by lia.
        rewrite div_mul by lia.
        lia.
      + replace (2 * n + 2 + 1) with (3 + n * 2) by lia.
        rewrite div_add by lia.
        simpl. lia.
  Qed.

  Lemma subtree_nat_leaf (t : bintree A) :
    complete t ->
    forall j, j > btsize t / 2 ->
         match subtree_nat t (j - 1) with
         | None => True
         | Some t' => leaf t'
         end.
  Proof.
    intros.
    assert (Hs : btsize t <= 1 \/ btsize t > 1) by lia.
    destruct Hs.
    - unfold subtree_nat.
      destruct t as [|x [] []]; simpl in H1; try lia.
      + destruct (decode (j - 1)); simpl; auto.
      + destruct (decode (j - 1)) as [| [] [] ]; simpl; auto.
    - eapply subtree_leaf; try assumption.
      unfold last_btidx.
      eapply btidx_lt_complete.
      rewrite encode_removelast.
      rewrite 2 encode_decode.
      rewrite sub_add by lia.
      assert (1 <= btsize t / 2)
        by (eapply (div_le_mono 2 _ 2); lia).
      lia.
  Qed.

  Lemma perfect_fromListAux (xss : list (list A)) :
    perfect_list 0 xss -> perfect' (fromListAux xss) (length xss).
  Proof.
    remember (length xss) as n.
    revert xss Heqn.
    induction n; intros.
    - destruct xss; try discriminate.
      rewrite unfold_fromListAux.
      constructor.
    - destruct xss as [|[|x xs] xss]; simpl in *; destruct H; try discriminate.
      rewrite unfold_fromListAux.
      econstructor.
      + eapply IHn.
        * rewrite splitLListLeft_length.
          lia.
        * eapply perfect_splitLListLeft. assumption.
      + eapply IHn.
        * rewrite splitLListRight_length' by assumption.
          lia.
        * eapply perfect_splitLListRight. assumption.
  Qed.

  Lemma complete_fromListAux (xss : list (list A)) :
    complete_list 0 xss -> complete' (fromListAux xss) (length xss).
  Proof.
    remember (length xss) as n.
    revert xss Heqn.
    induction n using Wf_nat.lt_wf_ind. intros.
    destruct n.
    - destruct xss; try discriminate.
      rewrite unfold_fromListAux.
      econstructor.
    - destruct xss as [|[|x xs] xss]; simpl in *; try discriminate; try lia.
      eapply succ_inj in Heqn. subst.
      rewrite unfold_fromListAux.
      destruct H0 as [[]|[]].
      + pose proof (complete_splitLList 0 xss H1).
        remember (length xss) as n'.
        remember (splitLListLeft 0 xss) as l.
        remember (splitLListRight 0 xss) as r.
        simpl in H2.
        destruct H2 as [[Hl1 [Hl2 [Hr1 Hr2]]] | [Hl1 [Hl2 [Hr1 Hr2]]]].
        * eapply complete_node_perfect_complete.
          -- rewrite <- Hl2.
             eapply perfect_fromListAux.
             assumption.
          -- eapply H; try lia; assumption.
        * destruct Hr2 as [n'' []].
          replace n' with (S n'') by lia.
          eapply complete_node_complete_perfect.
          -- eapply H; try lia; assumption.
          -- rewrite <- H2.
             eapply perfect_fromListAux.
             assumption.
      + subst. lia.
  Qed.

  Lemma complete_fromList (xs : list A) : complete (fromList xs).
  Proof.
    unfold complete, fromList.
    remember (toLList 0 xs) as xss.
    assert (H : complete_list 0 xss)
      by (subst; eapply complete_toLList).
    eexists. eapply complete_fromListAux. assumption.
  Qed.

  Lemma complete_toListAux_length n (t : bintree A) :
    complete' t n -> length (toListAux t) = n.
  Proof.
    intros.
    admit.
    (*
    induction H using complete_ind_ranked.
    - reflexivity.
    - simpl.
      rewrite zipLList_length.
      rewrite IHcomplete'1.
      rewrite IHcomplete'2.
      lia.
     *)
  Admitted.

  Lemma perfect_toListAux_list (t : bintree A) :
    perfect t -> perfect_list 0 (toListAux t).
  Proof.
    intros [n H].
    induction H.
    - simpl. auto.
    - simpl. split; auto.
      eapply perfect_zipLList; try assumption.
      erewrite complete_toListAux_length by (eapply perfect'2complete'; eassumption).
      erewrite complete_toListAux_length by (eapply perfect'2complete'; eassumption).
      reflexivity.
  Qed.

  Lemma complete_toListAux_list (t : bintree A) :
    complete t -> complete_list 0 (toListAux t).
  Proof.
    intros [n H].
    induction H; simpl.
    - auto.
    - left. split; auto.
      eapply complete_zipLList. left.
      split; [|split].
      + eapply perfect_toListAux_list. eexists. eassumption.
      + assumption.
      + erewrite complete_toListAux_length by (eapply perfect'2complete'; eassumption).
        erewrite complete_toListAux_length by eassumption.
        reflexivity.
    - left. split; auto.
      eapply complete_zipLList. right.
      split; [|split].
      + assumption.
      + eapply perfect_toListAux_list. eexists. eassumption.
      + erewrite complete_toListAux_length by eassumption.
        erewrite complete_toListAux_length by (eapply perfect'2complete'; eassumption).
        reflexivity.
  Qed.

  Lemma fromListAux_toListAux (t : bintree A) :
    complete t -> fromListAux (toListAux t) = t.
  Proof.
    intros [n H].
    revert t H.
    induction n as [n IH] using Wf_nat.lt_wf_ind; intros.
    inversion H; subst; clear H.
    - reflexivity.
    - rename n0 into n. simpl. rewrite unfold_fromListAux.
      assert (H :
                perfect_list 0 (toListAux l) /\
                complete_list 0 (toListAux r) /\
                length (toListAux l) = length (toListAux r)).
      { split; [|split].
        - eapply perfect_toListAux_list.
          eexists; eassumption.
        - eapply complete_toListAux_list.
          eexists; eassumption.
        - erewrite complete_toListAux_length by (eapply perfect'2complete'; eassumption).
          erewrite complete_toListAux_length by eassumption.
          reflexivity.
      }
      rewrite splitLeft_zip by auto.
      rewrite splitRight_zip by auto.
      erewrite (IH n).
      erewrite (IH n).
      reflexivity.
      + lia.
      + assumption.
      + lia.
      + eapply perfect'2complete'. assumption.
    - rename n0 into n. simpl. rewrite unfold_fromListAux.
      assert (H :
                complete_list 0 (toListAux l) /\
                perfect_list 0 (toListAux r) /\
                length (toListAux l) = 1 + length (toListAux r)).
      { split; [|split].
        - eapply complete_toListAux_list.
          eexists; eassumption.
        - eapply perfect_toListAux_list.
          eexists; eassumption.
        - erewrite complete_toListAux_length by eassumption.
          erewrite complete_toListAux_length by (eapply perfect'2complete'; eassumption).
          reflexivity.
      }
      rewrite splitLeft_zip by auto.
      rewrite splitRight_zip by auto.
      erewrite (IH (S n)).
      erewrite (IH n).
      reflexivity.
      + lia.
      + eapply perfect'2complete'. assumption.
      + lia.
      + assumption.
  Qed.

  Lemma fromList_toList (t : bintree A) :
    complete t -> fromList (toList t) = t.
  Proof.
    intros.
    unfold toList.
    unfold fromList.
    rewrite toLList_concat by (eapply complete_toListAux_list; assumption).
    eapply fromListAux_toListAux; assumption.
  Qed.

  Lemma subtree_index (tree : bintree A) t i :
    complete tree
    -> option_subtree i tree = Some t
    -> forall n, lookup (toList t) n = lookup (toList tree) (n + (encode i) * 2 ^ (length (decode n))).
  Admitted.

  Lemma toList_subtree (tree : bintree A) i : lookup (toList tree) i =
                                  match subtree_nat tree i with
                                  | None => None
                                  | Some t => option_root t
                                  end.
    Admitted.
  
  Theorem subtree_nat_Some_node (tree : bintree A) t i (t_nonempty : t <> BT_nil) :
    subtree_nat tree i = Some t <->
    match t with
    | BT_nil => False
    | BT_node x l r => HeapsortHeader.lookup (toList tree) i = Some x /\ subtree_nat tree (i * 2 + 1) = Some l /\ subtree_nat tree (i * 2 + 2) = Some r
    end.
  Admitted.

  Theorem subtree_lookup (tree : bintree A) t i
    (H_complete : complete tree)
    (H_subtree : subtree_nat tree i = Some t)
    : lookup (toList tree) i = option_root t.
  Admitted.  

  Corollary subtree_nat_range (tree : bintree A) t i
    (H_complete : complete tree)
    (H_subtree : subtree_nat tree i = Some t)
    : i < btsize tree <-> t <> BT_nil.
  Proof.
    pose proof (subtree_lookup tree t i H_complete H_subtree) as claim1.
    destruct t as [ | x l r]; [apply nth_error_None in claim1 | apply isSome_intro, nth_error_Some in claim1]; rewrite toList_length in claim1.
    - split; [lia | contradiction].
    - split; [discriminate | lia].
  Qed.

  Lemma option_subtree_swap (tree : bintree A) i j k :
    k > i -> k > j ->
    subtree_nat (fromList (swap (toList tree) i j)) k = subtree_nat tree k.
  Admitted.
  
  Lemma btpartial_removelast (t : bintree A) :
    complete t ->
    btpartial t (fromList (removelast (toList t))).
  Proof.
    intros.
    rewrite <- (fromList_toList t H) at 1.
    destruct t.
    - vm_compute. econstructor.
    - remember (toList (BT_node x t1 t2)) as xs.
      assert (xs <> [])
        by (intro; subst; discriminate).
      rewrite (app_removelast_last x H0) at 1.
      eapply btpartial_fromList.
  Qed.

  Local Hint Resolve perfect'2complete' bteq_refl bteq_sym : core.

  Lemma shape_eq_perfect' (t t' : bintree A) :
    bteq_shape t t' ->
    forall rk : nat,
    perfect' t rk ->
    perfect' t' rk.
  Proof with eauto.
    intros t_shape_eq_t'.
    induction t_shape_eq_t' as [ | x l r x' l' r' l_shape_eq_l' IH_l r_shape_eq_r' IH_r]; intros rk t_shape_eq_t'...
    inversion t_shape_eq_t'; subst; clear t_shape_eq_t'; [econstructor 2]...
  Qed.

  Local Hint Resolve perfect'2complete' shape_eq_perfect' : core.

  Lemma shape_eq_complete' (t t' : bintree A) :
    bteq_shape t t' ->
    forall rk : nat,
    complete' t rk ->
    complete' t' rk.
  Proof with eauto.
    intros t_shape_eq_t'.
    induction t_shape_eq_t' as [ | x l r x' l' r' l_shape_eq_l' IH_l r_shape_eq_r' IH_r]; intros rk t_shape_eq_t'...
    inversion t_shape_eq_t'; subst; [constructor 2 | constructor 3]...
  Qed.

  Local Hint Resolve shape_eq_complete' : core.

  Theorem shape_eq_complete (t t' : bintree A) (t_shape_eq_t' : bteq_shape t t')
    : complete t <-> complete t'.
  Proof. split; intros [rk H_complete']; exists (rk); eauto. Qed.

End CompleteBinaryTree.

Section HeapProperty.

  Context {A : Type}.
  Variable R : A -> A -> Prop.

  Lemma heap_erase_priority p t : heap_pr R p t -> heap R t.
  Proof. intros. destruct H; econstructor; assumption. Qed.

  Lemma heap_pr_if_heap (R_refl : forall x, R x x) t : t <> BT_nil -> heap R t -> exists p, heap_pr R p t.
  Proof.
    intros Ht Hₕ.
    destruct Hₕ; try contradiction.
    eexists.
    econstructor; try assumption.
    eapply R_refl.
  Qed.

  Lemma heap_at_0 t : heap_at R 0 t -> heap R t.
  Proof.
    Local Transparent decodeIdx.
    unfold heap_at. simpl. tauto.
  Qed.

  Lemma heap_if_leaf t : leaf t -> heap R t.
  Proof.
    intro H. destruct t.
    - econstructor.
    - simpl in H. destruct H. subst. econstructor; econstructor.
  Qed.

  Lemma heap_at_leaves t : complete t -> forall j, j > btsize t / 2 -> heap_at R (j - 1) t.
  Proof.
    intros H j Hj. unfold heap_at.
    assert (H1 := subtree_nat_leaf t H j Hj).
    destruct (subtree_nat t (j-1)).
    - eapply heap_if_leaf; assumption.
    - auto.
  Qed.

  Lemma heap_btpartial t t' :
    btpartial t t' -> heap R t -> heap R t'.
  Proof.
    intro H. induction H as [| x l r l' r' Hl IHl Hr IHr |].
    - auto.
    - intros Hₕ.
      remember (BT_node x l r) eqn: E.
      destruct Hₕ; try discriminate.
      inversion E; subst; clear E.
      econstructor.
      + inversion Hl; subst; simpl in *; auto.
      + inversion Hr; subst; simpl in *; auto.
      + eapply IHl. assumption.
      + eapply IHr. assumption.
    - constructor.
  Qed.

  Lemma removelast_heap t :
    complete t -> heap R t -> heap R (fromList (removelast (toList t))).
  Proof.
    intros. eapply heap_btpartial.
    - eapply btpartial_removelast. assumption.
    - assumption.
  Qed.

  Lemma heap_rel p t :
    Transitive R ->
    heap_pr R p t ->
    forall x, btin x t -> R p x.
  Proof.
    intro T.
    induction t.
    - intros. inversion H0.
    - intros.
      remember (BT_node x t1 t2) as t eqn: E.
      destruct H; try discriminate.
      inversion E; subst; clear E.
      remember (BT_node x t1 t2) as t eqn: E.
      destruct H0; inversion E; subst; clear E.
      + assumption.
      + eapply IHt1.
        * destruct heap_l; econstructor; try assumption.
          transitivity x; assumption.
        * assumption.
      + eapply IHt2.
        * destruct heap_r; econstructor; try assumption.
          transitivity x; assumption.
        * assumption.
  Qed.

  Lemma heap_head_last t x xs a :
    Reflexive R ->
    Transitive R ->
    heap R t ->
    toList t = x :: xs ->
    R x (last (toList t) a).
  Proof.
    intros.
    eapply heap_rel.
    - assumption.
    - instantiate (1 := t).
      destruct H1; try discriminate.
      unfold toList in H2.
      simpl in H2. inversion H2; subst.
      econstructor; try assumption.
      eapply H.
    - eapply toList_btin.
      eapply In_last.
      intro. rewrite H3 in H2. discriminate.
  Qed.

End HeapProperty.

Section BinaryTreeZipper.

  Context {A : Type}.

  Inductive occurs (t : bintree A) : btidx -> bintree A -> Prop :=
  | Occurs_0
    : occurs t [] t
  | Occurs_l ds x l r
    (H_l : occurs t ds l)
    : occurs t (Dir_left :: ds) (BT_node x l r)
  | Occurs_r ds x l r
    (H_r : occurs t ds r)
    : occurs t (Dir_right :: ds) (BT_node x l r).

  Local Hint Constructors occurs : core.

  Lemma occurs_refl root :
    occurs root [] root.
  Proof. eauto. Qed.

  Lemma occurs_trans root :
    forall ds t,
    occurs t ds root ->
    forall ds' t',
    occurs t' ds' t ->
    occurs t' (ds ++ ds') root.
  Proof. intros ds1 t1 X1 ds2 t2 X2; revert ds2 t2 X2. induction X1; simpl; eauto. Qed.

  Lemma occurs_iff ds t root :
    occurs t ds root <->
    option_subtree ds root = Some t.
  Proof with discriminate || eauto.
    split. intros X; induction X...
    revert t root.
    induction ds as [ | [ | ] ds IH]; simpl; intros t root H_eq.
    { apply Some_inj in H_eq; subst t... }
    all: destruct root as [ | x l r]...
  Qed.

  Lemma complete_occurs ds t root
    (H_occurs : occurs t ds root)
    (H_complete : complete root)
    : complete t.
  Proof with eauto.
    revert H_occurs H_complete.
    intros X; induction X; intros H_complete...
    - exact (IHX (proj1 (destruct_complete _ H_complete))).
    - exact (IHX (proj2 (destruct_complete _ H_complete))).
  Qed.

  Lemma complete_subtree_nat (tree : bintree A) (H_complete : complete tree)
    : forall i t, subtree_nat tree i = Some t -> complete t.
  Proof.
    intros i t H_subtree. apply occurs_iff in H_subtree.
    now apply complete_occurs with (ds := decode i) (root := tree).
  Qed.

  Lemma occurs_recover_bintree g t
    : occurs t (btctx2idx g) (recover_bintree g t).
  Proof with eauto.
    revert t. induction g as [ | x r g IH | x l g IH]; simpl; [intros t | intros l | intros r].
    all: try eapply occurs_trans. all: try exact (IH (BT_node x l r)). all: repeat econstructor.
  Qed.

  Theorem complete_recover (tree : bintree A) (H_complete : complete tree)
    : forall g t, recover_bintree g t = tree -> complete t.
  Proof.
    intros g t H_recover.
    eapply complete_occurs.
    - apply occurs_recover_bintree. 
    - rewrite <- H_recover in H_complete; eassumption.
  Qed.

  Lemma recover_preserves_bteq_shape (t t' : bintree A) (H_shape_eq : bteq_shape t t')
    : forall g, bteq_shape (recover_bintree g t) (recover_bintree g t').
  Proof with eauto.
    intros g. revert t t' H_shape_eq.
    induction g as [ | x r g IH | x l g IH]; simpl; intros t t' H_shape_eq...
    all: apply IH; econstructor 2... all: apply bteq_refl.
  Qed.

  Theorem equicomplete_thm (g : btctx A) t t' (H_shape_eq : bteq_shape t t')
    : complete (recover_bintree g t) <-> complete (recover_bintree g t').
  Proof. apply shape_eq_complete, recover_preserves_bteq_shape, H_shape_eq. Qed.

  Lemma recover_focus (g : btctx A) t i :
    let '(g', t') := focus g t i in
    recover_bintree g t = recover_bintree g' t'.
  Proof.
    revert g t.
    induction i.
    - intros g t. destruct t; reflexivity.
    - intros g t.
      destruct t, a; try reflexivity; simpl.
      + pose proof (IHi (btctx_left x t2 g) t1).
        destruct (focus (btctx_left x t2 g) t1 i) as [g' t'].
        auto.
      + pose proof (IHi (btctx_right x t1 g) t2).
        destruct (focus (btctx_right x t2 g) t2 i) as [g' t'].
        auto.
  Qed.

  Lemma focus_recover (tree : bintree A) t i j:
    let '(g', _) := focus btctx_top tree (decode i) in
    if j =? i
    then focus btctx_top (recover_bintree g' t) (decode j) = (g', t)
    else if j =? (i * 2 + 1)
         then match t with
              | BT_nil => True
              | BT_node x l r =>
                  focus btctx_top (recover_bintree g' t) (decode j) = (btctx_left x r g', l)
              end
         else if j =? (i * 2 + 2)
              then match t with
                   | BT_nil => True
                   | BT_node x l r =>
                       focus btctx_top (recover_bintree g' t) (decode j) = (btctx_right x l g', r)
                   end
              else True.                                               
  Admitted.

   Lemma swap_subtree_left (tree : bintree A) i :
    fromList (swap (toList tree) (i * 2 + 1) i) =
      match focus btctx_top tree (decode i) with
      | (_, BT_nil) => tree
      | (_, BT_node x BT_nil _) => tree
      | (g, BT_node x (BT_node xl ll lr) r) => recover_bintree g (BT_node xl (BT_node x ll lr) r)
      end.
  Admitted.
  
  Lemma swap_subtree_right (tree : bintree A) i :
    fromList (swap (toList tree) (i * 2 + 2) i) =
      match focus btctx_top tree (decode i) with
      | (_, BT_nil) => tree
      | (_, BT_node x _ BT_nil) => tree
      | (g, BT_node x l (BT_node xr rl rr)) => recover_bintree g (BT_node xr l (BT_node x rl rr))
      end.
  Admitted.

  Lemma recover_option_subtree (g : btctx A) t :
    option_subtree (btctx2idx g) (recover_bintree g t) = Some t.
  Admitted.
  
  Lemma btctx2idx_focus (tree : bintree A) i : let '(g, _) := focus btctx_top tree i in btctx2idx g = i.
  Admitted.
  
  Theorem btctx_lookup (g : btctx A) t :
    lookup (toList (recover_bintree g t)) (encode (btctx2idx g)) = option_root t.
  Admitted.

  Theorem recover_upd_root_repr_upd (t : bintree A) k g :
    t <> BT_nil ->
    toList (recover_bintree g (upd_root k t)) =
    upd (toList (recover_bintree g t)) (encode (btctx2idx g)) k.
  Admitted.

  Lemma recover_complete g (t : bintree A) :
    complete (recover_bintree g t) -> complete t.
  Admitted.

End BinaryTreeZipper.

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
    intros i.
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
    intros i.
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

  Lemma listExt_skipn {A : Type} (xs : list A) (n : nat) :
    forall i, lookup (skipn n xs) i = lookup xs (n + i).
  Proof with eauto.
    unfold lookup. revert n. induction xs as [ | x xs IH]; intros [ | n']; simpl... now destruct i.
  Qed.

  Lemma listExt_combine {A : Type} {B : Type} (xs : list A) (ys : list B) :
    forall i,
    match lookup (combine xs ys) i with
    | None => i >= length xs \/ i >= length ys
    | Some (x, y) => lookup xs i = Some x /\ lookup ys i = Some y
    end.
  Proof with discriminate || eauto.
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
    intros i; unfold add_indices.
    assert (claim1 := listExt_combine xs (seq 0 (length xs)) i).
    destruct (nth_error (combine xs (seq 0 (length xs))) i) as [[x n] | ] eqn: H_obs.
    - destruct claim1 as [H_obs_xs H_obs_seq]; split...
      assert (claim2 := listExt_seq 0 (length xs) i).
      rewrite H_obs_seq in claim2...
    - rewrite seq_length in claim1.
      rewrite nth_error_None; lia.
  Qed.

  Lemma listExt_swap {A : Type} (xs : list A) (i1 : nat) (i2 : nat) :
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
    intros H_i1 H_i2.
    assert (H_lookup_i1 := proj2 (nth_error_Some xs i1) H_i1).
    assert (H_lookup_i2 := proj2 (nth_error_Some xs i2) H_i2).
    intros i; cbn; unfold swap.
    assert (claim1 := listExt_map (uncurry (swap_aux xs i1 i2)) (add_indices xs) i).
    rewrite claim1; unfold option_map.
    assert (claim2 := listExt_add_indices xs i).
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

  Lemma add_indices_length {A : Type} (xs : list A) :
    length (add_indices xs) = length xs.
  Proof with lia || discriminate || eauto.
    transitivity (length (map snd (add_indices xs))).
    { symmetry. apply map_length. }
    transitivity (length (seq 0 (length xs))).
    { apply f_equal. apply list_extensionality.
      intros i.
      rewrite (listExt_map snd (add_indices xs) i).
      assert (claim1 := listExt_add_indices xs i).
      assert (claim2 := listExt_seq 0 (length xs) i).
      destruct (lookup (add_indices xs) i) as [[x n] | ] eqn: H_obs.
      - destruct claim1 as [H_eq H_obs_xs].
        subst n. simpl. symmetry.
        destruct (lookup (seq 0 (length xs)) i) as [i_ | ]; subst...
        apply isSome_intro, nth_error_Some in H_obs_xs...
      - destruct claim1 as [H_eq H_obs_xs].
        simpl. symmetry. apply nth_error_None. rewrite seq_length...
    }
    rewrite seq_length...
  Qed.

  Lemma listExt_upd {A : Type} (xs : list A) (i1 : nat) (x1 : A) :
    i1 < length xs ->
    forall i,
    match lookup (upd xs i1 x1) i with
    | None => i >= length xs
    | Some val => Some val = if Nat.eq_dec i i1 then Some x1 else lookup xs i
    end.
  Proof with discriminate || eauto.
    intros H_i1.
    assert (H_lookup_i1 := proj2 (nth_error_Some xs i1) H_i1).
    intros i; cbn; unfold upd.
    assert (claim1 := listExt_map (fun '(x, i0) => if eq_dec i0 i1 then x1 else x) (add_indices xs) i).
    rewrite claim1; unfold option_map.
    assert (claim2 := listExt_add_indices xs i).
    destruct (nth_error (add_indices xs) i) as [[x n] | ] eqn: H_obs_add_indices.
    - destruct claim2 as [H_eq1 H_eq2]; subst n.
      destruct (Nat.eq_dec i i1) as [H_yes1 | H_no1]...
    - exact (proj1 claim2).
  Qed.

  Theorem upd_spec {A : Type} (xs : list A) i x :
    upd xs i x = if Nat.ltb i (length xs) then firstn i xs ++ [x] ++ skipn (i + 1) xs else xs.
  Proof with lia || eauto.
    rename i into i0, x into x0.
    destruct (Nat.ltb i0 (length xs)) eqn: H_range.
    - apply Nat.ltb_lt in H_range.
      assert (claim1 := listExt_upd xs i0 x0 H_range).
      transitivity (firstn i0 xs ++ (firstn 1 (x0 :: skipn (S i0) xs) ++ skipn 1 (x0 :: skipn (S i0) xs))).
      2: rewrite firstn_skipn; replace (i0 + 1) with (S i0)...
      transitivity (firstn i0 (upd xs i0 x0) ++ skipn i0 (upd xs i0 x0)).
      1: symmetry; apply firstn_skipn.
      f_equal.
      { apply list_extensionality.
        intros i. specialize (claim1 i).
        assert (claim2 := listExt_firstn (upd xs i0 x0) i0 i).
        destruct (lookup (firstn i0 (upd xs i0 x0)) i) as [x | ] eqn: H_obs.
        - destruct claim2 as [H_i_lt_i0 H_x].
          rewrite H_x in claim1.
          destruct (Nat.eq_dec i i0) as [H_yes1 | H_no1]...
          rewrite claim1. symmetry. apply firstn_nth_error...
        - symmetry. apply nth_error_None. rewrite firstn_length.
          enough (to_show : i >= i0 \/ i >= length xs)...
          unfold upd in claim2. rewrite map_length in claim2.
          rewrite add_indices_length in claim2...
      }
      { apply list_extensionality.
        intros i.
        rewrite listExt_skipn.
        destruct i as [ | i'].
        - rewrite Nat.add_0_r. simpl.
          specialize (claim1 i0).
          destruct (lookup (upd xs i0 x0) i0) as [x | ]...
          destruct (Nat.eq_dec i0 i0)...
        - rewrite firstn_skipn.
          replace ((S i')) with (1 + i') at 2 by lia.
          rewrite <- listExt_skipn with (xs0 := (x0 :: skipn (S i0) xs)).
          set (xs_suffix := skipn (S i0) xs).
          simpl. unfold xs_suffix. specialize (claim1 (i0 + S i')).
          destruct (lookup (upd xs i0 x0) (i0 + S i')) as [x | ].
          + destruct (Nat.eq_dec (i0 + S i') i0) as [H_yes1 | H_no1]...
            rewrite claim1. replace (i0 + S i') with (S i0 + i')...
            symmetry. apply listExt_skipn.
          + symmetry. apply nth_error_None.
            rewrite skipn_length...
      }
    - apply Nat.ltb_nlt in H_range.
      unfold upd. apply list_extensionality. intros i.
      rewrite (listExt_map (fun '(x, i1) => if eq_dec i1 i0 then x0 else x) (add_indices xs) i).
      assert (claim1 := listExt_add_indices xs i).
      destruct (lookup (add_indices xs) i) as [[x n] | ] eqn: H_obs.
      + destruct claim1 as [H_eq H_obs_xs]; subst.
        simpl. destruct (Nat.eq_dec n i0); [subst n | ]...
        apply isSome_intro, nth_error_Some in H_obs_xs...
      + simpl. now symmetry.
  Qed.

  Lemma upd_length {A : Type} (xs : list A) i0 x0 : length (upd xs i0 x0) = length xs.
  Proof. unfold upd. rewrite map_length. apply add_indices_length. Qed.

End ListAccessories.
