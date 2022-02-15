Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import HeapsortHeader.
Require Import Heapsort1 Heapsort2.
Require Import HTactics ProofMode.
Require Import SimModSem.
Require Import Coq.Sorting.Sorted.

Set Implicit Arguments.

Ltac steps_weak := repeat (prep; try _step; simpl).

Lemma unfold_iter_eq:
  ∀ (E : Type → Type) (A B : Type) (f : A → itree E (A + B)) (x : A),
    ITree.iter f x = ` lr : A + B <- f x;; match lr with
                                          | inl l => tau;; ITree.iter f l
                                          | inr r => Ret r
                                          end.
Proof. intros. eapply bisim_is_eq. eapply unfold_iter. Qed.

Section SIMMODSEM.

  Context `{Σ : GRA.t}.

  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb HeapsortStb) (GlobalStb sk).
  Hint Unfold HeapsortStb : stb.

  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => True)%I.

  Lemma sim_create (sk : alist string Sk.gdef) :
    sim_fnsem wf top2
   ("create",
   fun_to_tgt "Heapsort" (GlobalStb sk) {| fsb_fspec := create_spec; fsb_body := fun _ => triggerNB |})
   ("create", cfunU Heapsort1.create_body).
  Proof.
    init. harg. destruct x as [tree initial]. mDesAll. clear PURE1.
    destruct PURE0 as [? [PURE2 [PURE3 PURE4]]];subst. steps.
    astop.
    deflag. revert mrp_src mp_tgt WF ctx ACC PURE2 initial PURE3 PURE4 mr_src mp_src.
    induction tree;i.
    - unfold toList. 
      rewrite unfold_iter_eq.
      destruct (initial + (initial + 0) <=? strings.length (concat (toListAux BT_nil))) eqn:E
      ;simpl in PURE3;assert (contra : 1 <= 0) by nia;inversion contra.
    - assert (PURE2_1 : complete tree1).
      {destruct PURE2 as [d PURE2]. inversion PURE2;subst;
          [apply perfect'2complete' in H_l;exists n|exists (S n)];apply H_l.}
      assert (PURE2_2 : complete tree2).
      {destruct PURE2 as [d PURE2]. inversion PURE2;subst;
          [exists n|apply perfect'2complete' in H_r;exists n];apply H_r.}
      unfold toList. rewrite unfold_iter_eq. simpl.
      destruct (initial + (initial + 0) <=?
                 S (strings.length (concat (zip_exp (toListAux tree1) (toListAux tree2)))))
               eqn:E.
      destruct (initial + (initial + 0) <=?
                 strings.length (concat (zip_exp (toListAux tree1) (toListAux tree2))))
               eqn:E1.
      + steps.
        pose proof (IHtree1 _ _ WF _ ACC PURE2_1) as IH1;clear IHtree1.
        pose proof (IHtree2 _ _ WF _ ACC PURE2_2) as IH2;clear IHtree2.
        clear E. apply leb_complete in E1.
        assert (Y : ∀ (root : bintree Z),
                   complete root
                   ->
                     forall i, (i < length (toList root)
                   → match HeapsortHeader.lookup (toList root) i with
                     | None => subtree_nat root i = None
                     | Some x => exists t, (subtree_nat root i = Some t /\ option_root t = Some x)
                     end)). { admit "lookup_is_subtree_nat".}
        pose proof (Y _ PURE2 (initial * 2 - 1)) as U.
        simpl in U. assert (T : initial * 2 - 1 < S (strings.length (concat (zip_exp (toListAux tree1) (toListAux tree2))))) by nia. apply U in T. clear U.
        destruct (HeapsortHeader.lookup (toList (BT_node x tree1 tree2)) (initial * 2 - 1))
                 eqn:P.
        * destruct T as [t [T1 T2]]. rewrite <- P in T2. simpl in P. rewrite P.
          assert (K : exists n st, subtree_nat t n = Some st -> )
          admit "maybe guilty".
        * assert (D : forall j (t : bintree Z),
                     complete t -> subtree_nat t j = Some BT_nil \/ subtree_nat t j = None
                     -> j >= btsize t).
          {admit "comp_outrange_rev".}
          pose proof (D _ _ PURE2 (or_intror T)) as E.
          assert (Q : initial * 2 - 1 >= S (strings.length (concat (zip_exp (toListAux tree1) (toListAux tree2)))) -> False) by nia. 
          rewrite <- toList_length in E. simpl in E. apply Q in E. inversion E.
      +
        
        
        pose proof (Y (BT_node x tree1 tree2 (initial * 2 -1))) as U. simpl in U.
    (* steps. rewrite unfold_iter_eq.
       destruct l;nia.
     *)  
    (*
      destruct H0. destruct H0. steps. rewrite unfold_iter_eq.
      destruct (l + (l + 0) <=? S n);destruct (l + (l + 0) <=? n).
      + unfold toList. rewrite toList_step_unfold. steps.
     *)
  Admitted.

  Lemma sim_heapify (sk : alist string Sk.gdef) :
    sim_fnsem wf top2
              ("heapify",
               fun_to_tgt "Heapsort" (GlobalStb sk) {| fsb_fspec := heapify_spec; fsb_body := fun _ => triggerNB |})
              ("heapify", cfunU Heapsort1.heapify_body).
  Proof with lia || eauto. (*
  (** entering function *)
    Opaque div swap.
    init. harg. destruct x as [[root p] k]. mDesAll; subst.
    clear PURE1. destruct PURE0 as [? [PURE1 [PURE2 [PURE3 PURE4]]]]; subst.
    steps. astop. steps.
  (** entering 1st loop *)
    (* loop-invariant *)
    remember (k :: list.tail (toList root), 1) as i eqn: H_init; destruct i as [xs0 par_i0].
    remember (fromList xs0) as t eqn: t_is.
    assert (H_t_init : xs0 = toList t) by now rewrite t_is; rewrite toList_fromList.
    assert (H_xs_init : xs0 = k :: list.tail (toList root)) by congruence.
    assert (H_t_perm : xs0 ≡ₚ k :: list.tail (toList root)) by now rewrite <- H_xs_init; eapply Permutation_refl.
    assert (H_par_i_positive : par_i0 > 0) by now replace par_i0 with 1 by congruence; lia.
    assert (H_t_lookup : HeapsortHeader.subtree_nat (fromList xs0) (par_i0 - 1) = Some t).
    { replace par_i0 with 1; [rewrite t_is | congruence]... }
    assert (H_recover : recover_bintree btctx_top t = fromList xs0).
    { rewrite t_is... }
    remember (btctx_top) as cur_ctx eqn: H_ctx in H_recover.
    clear H_init t_is H_t_init H_xs_init H_ctx.
    (* execute loop *)
    deflag. revert mrp_src mp_tgt WF ctx mr_src mp_src PURE1 PURE2 PURE3 ACC xs0 par_i0 H_par_i_positive H_t_perm H_recover H_t_lookup.
    induction t as [ | x l IH_l r IH_r]; i.
    - rewrite unfold_iter_eq.
      destruct (par_i0 * 2 <=? strings.length (toList root)) eqn: H_obs1.
      1:{ admit "impossible". }
      { steps.
        remember BT_nil as t eqn: t_is in H_recover, H_t_lookup. clear H_obs1 t_is.
        deflag. revert p k PURE4 mrp_src mp_tgt WF ctx mr_src mp_src PURE1 PURE2 PURE3 ACC xs0 par_i0 H_par_i_positive H_t_perm t H_recover H_t_lookup.
        induction cur_ctx as [ | x r g IH | x l g IH]; i.
        - assert (H_end : par_i0 = 1) by admit "trivial".
          rewrite unfold_iter_eq. steps. admit "escaping function".
        - rewrite unfold_iter_eq. steps.
          destruct ((par_i0 =? 1)%nat) eqn: H_obs2.
          1:{ admit "impossible". }
          steps. destruct (HeapsortHeader.lookup xs0 (par_i0 `div` 2 - 1)) as [x_p |] eqn: H_obs3.
          2:{ admit "impossible". }
          steps. destruct ((k <? x_p)%Z) eqn: H_obs4.
          + steps. admit "escaping function".
          + steps. deflag. eapply IH...
            admit "par_i0 `div` 2 > 0".
            admit "swap xs0 (par_i0 - 1) (par_i0 `div` 2 - 1) ≡ₚ k :: list.tail (toList root)".
            admit "recover_bintree g ?t = fromList (swap xs0 (par_i0 - 1) (par_i0 `div` 2 - 1))".
            admit "subtree_nat (fromList (swap xs0 (par_i0 - 1) (par_i0 `div` 2 - 1))) (par_i0 `div` 2 - 1) = Some ?t".
        - rewrite unfold_iter_eq. steps.
          destruct ((par_i0 =? 1)%nat) eqn: H_obs2.
          1:{ admit "impossible". }
          steps. destruct (HeapsortHeader.lookup xs0 (par_i0 `div` 2 - 1)) as [x_p |] eqn: H_obs3.
          2:{ admit "impossible". }
          steps. destruct ((k <? x_p)%Z) eqn: H_obs4.
          + steps. admit "escaping function".
          + steps. deflag. eapply IH...
            admit "par_i0 `div` 2 > 0".
            admit "swap xs0 (par_i0 - 1) (par_i0 `div` 2 - 1) ≡ₚ k :: list.tail (toList root)".
            admit "recover_bintree g ?t0 = fromList (swap xs0 (par_i0 - 1) (par_i0 `div` 2 - 1))".
            admit "subtree_nat (fromList (swap xs0 (par_i0 - 1) (par_i0 `div` 2 - 1))) (par_i0 `div` 2 - 1) = Some ?t0".
      }
    - rewrite unfold_iter_eq.
      destruct (par_i0 * 2 <=? strings.length (toList root)) eqn: H_obs1.
      2:{ admit "impossible". }
      destruct (strings.length (toList root)).
      1:{ admit "impossible". }
      steps.
      destruct (HeapsortHeader.lookup xs0 (par_i0 * 2 - 1)) as [x_l | ] eqn: H_obs_l.
      2:{ admit "impossible". }
      destruct (HeapsortHeader.lookup xs0 (par_i0 * 2)) as [x_r | ] eqn: H_obs_r.
      2:{ admit "impossible". }
      steps. destruct (par_i0 * 2 <=? n) eqn: H_obs2.
      + steps. destruct ((x_l <? x_r)%Z) eqn: H_obs3.
        { deflag. eapply IH_r...
          admit "swap xs0 (par_i0 * 2 + 1 - 1) (par_i0 - 1) ≡ₚ k :: list.tail (toList root)".
          admit "recover_bintree cur_ctx r = fromList (swap xs0 (par_i0 * 2 + 1 - 1) (par_i0 - 1))".
          admit "subtree_nat (fromList (swap xs0 (par_i0 * 2 + 1 - 1) (par_i0 - 1))) (par_i0 * 2 + 1 - 1) = Some r".
        }
        { deflag. eapply IH_l...
          admit "swap xs0 (par_i0 * 2 - 1) (par_i0 - 1) ≡ₚ k :: list.tail (toList root)".
          admit "recover_bintree cur_ctx l = fromList (swap xs0 (par_i0 * 2 - 1) (par_i0 - 1))".
          admit "subtree_nat (fromList (swap xs0 (par_i0 * 2 - 1) (par_i0 - 1))) (par_i0 * 2 - 1) = Some l".
        }
      + steps. deflag. eapply IH_l...
        admit "swap xs0 (par_i0 * 2 - 1) (par_i0 - 1) ≡ₚ k :: list.tail (toList root)".
        admit "recover_bintree cur_ctx l = fromList (swap xs0 (par_i0 * 2 - 1) (par_i0 - 1))".
        admit "subtree_nat (fromList (swap xs0 (par_i0 * 2 - 1) (par_i0 - 1))) (par_i0 * 2 - 1) = Some l". *)
  Admitted.

  Lemma sim_heapsort (sk : alist string Sk.gdef) :
    sim_fnsem wf top2
              ("heapsort", fun_to_tgt "Heapsort" (GlobalStb sk) {| fsb_fspec := heapsort_spec; fsb_body := fun _ => triggerNB|})
              ("heapsort", cfunU Heapsort1.heapsort_body).
  Proof.
    Opaque div.
    unfold Heapsort1.heapsort_body.
    init.
    harg. rename x into xs. mDesAll. clear PURE1. steps.

    remember (length xs <=? 1) as b.
    destruct b.
    (* input is trivially sorted when length xs <= 1 *)
    { astop. steps. force_l. eexists. steps.
      hret tt; ss.
      iModIntro. iSplit; ss. iPureIntro. esplits; try reflexivity.
      destruct xs as [| x []]; try discriminate.
      - econs.
      - econs; econs.
    }

    (* when length xs > 1 *)
    assert (Hxs : length xs > 1)
      by (eapply leb_complete_conv; et).
    clear Heqb.
    steps.

    (* set tree and it's initial condition *)
    remember (fromList xs) as tree.
    set (xs0 := xs). unfold xs0 at 1.
    replace xs0 with (toList tree)
      by (subst; eapply toList_fromList).
    clear xs0.
    assert (Hₚ : toList tree ≡ₚ xs)
      by (subst; rewrite toList_fromList; eapply Permutation_refl).
    assert (Hc : complete tree)
      by (subst; eapply complete_fromList).
    clear Heqtree.

    (* set l and it's initial condition *)
    remember (length (toList tree) / 2) as l.
    rewrite toList_length in Heql.
    assert (Hₗ : l <= btsize tree).
    { subst.
      rewrite <- toList_length.
      eapply Nat.lt_le_incl.
      eapply Nat.div_lt.
      - replace (length (toList tree)) with (length xs)
          by (eapply Permutation_length; symmetry; ss).
        lia.
      - lia.
    }
    assert (Hₕ : forall j, j > l -> heap_at Z.ge (j - 1) tree)
      by (subst; eapply heap_at_leaves; assumption).
    clear Heql.

    (* 'l' for first loop, 'length xs' for second loop *)
    astart (l + length xs).

    deflag.
    revert tree Hₚ Hₗ Hc Hₕ w ctx mp_src mp_tgt mr_src WF ACC.
    induction l.
    (* first loop *)
    2: {
      i. rewrite unfold_iter_eq. steps.
      acatch.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1 := l + length xs).
        eapply OrdArith.lt_from_nat.
        lia.
      }
      hcall (tree, S l) _ with "".
      { iModIntro. iSplit; ss. iPureIntro. splits; ss; try lia.
      }
      { ss. splits; et; oauto. }
      mDesAll. rename a into tree'. des. steps.
      rewrite Nat.sub_0_r.
      deflag.
      eapply IHl.
      - symmetry in PURE3. transitivity (toList tree); ss.
      - rewrite <- toList_length.
        rewrite <- toList_length in Hₗ.
        replace (length (toList tree')) with (length (toList tree))
          by (eapply Permutation_length; ss).
        lia.
      - assumption.
      - intros. eapply PURE4. lia.
      - red. inversion WF. econs. et.
      - assumption.
    }

    i. rewrite unfold_iter_eq. steps.
    clear Hₗ.

    (* useful hint for lia *)
    assert (H_size : length xs = btsize tree).
    { erewrite Permutation_length by (symmetry; eapply Hₚ).
      eapply toList_length.
    }

    (* assert heap_pr from heap_at *)
    rename Hₕ into H.
    assert (Hₕ : heap Z.ge tree)
      by (eapply H with (j := 1); lia).
    eapply heap_pr_if_heap in Hₕ; try lia.
    destruct Hₕ as [p Hₕ].
    clear H.

    (* set ys *)
    remember ([] : list Z) as ys.
    rename Hₚ into H.
    assert (Hₚ : toList tree ++ ys ≡ₚ xs)
      by (subst; rewrite app_nil_r; assumption).
    assert (Hₛ : Sorted Z.le ys)
      by (subst; econs).
    assert (H_head : match ys with
                     | [] => True
                     | y :: ys => y = p
                     end) by (subst; auto).
    clear H Heqys.

    (* set induction variable, l *)
    remember (btsize tree - 1) as l.
    assert (Hₗ : btsize tree = l + 1) by lia.
    replace (length xs) with (l + 1) by lia.
    clear Heql.

    clear H_size.

    deflag.
    revert tree p ys Hₚ Hₛ Hc H_head Hₕ Hₗ w ctx mp_src mp_tgt mr_src WF ACC.
    induction l.
    (* second loop *)
    2: {
      i. rewrite unfold_iter_eq. steps.
      rewrite toList_length.
      replace (btsize tree <=? 1) with false
        by (symmetry; eapply leb_correct_conv; lia).
      steps.
      assert (H : match tree with
                  | BT_nil => False
                  | BT_node p _ _ => toList tree = p :: tail (toList tree)
                  end)
        by (eapply toList_step; lia).
      destruct tree as [| q tree1 tree2 ] eqn: Etree; try contradiction.
      rewrite <- Etree in *.
      set (xs1 := toList tree) in *.
      unfold xs1 at 3.
      rewrite Etree.
      assert (H_length : length xs1 = l + 2)
        by (subst xs1; rewrite toList_length; lia).
      steps_weak.
      acatch.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1 := l + 1).
        eapply OrdArith.lt_from_nat.
        lia.
      }
      hcall (fromList (removelast xs1), q, last xs1 0%Z) _ with "".
      { iModIntro. iSplit; auto. iPureIntro. esplits.
        - rewrite toList_fromList. reflexivity.
        - eapply complete_fromList.
        - assert (tail xs1 <> []).
          { destruct xs1 as [| x [] ]; simpl in H_length; try lia.
            auto.
          }
          rewrite H. simpl. destruct (tail xs1); try contradiction.
          reflexivity.
        - eapply heap_head_last.
          + unfold Reflexive. lia.
          + unfold Transitive. lia.
          + eapply heap_erase_priority. eassumption.
          + subst xs1. eassumption.
        - eapply heap_erase_priority in Hₕ.
          subst.
          eapply removelast_heap.
          assumption.
        - reflexivity.
      }
      { ss. splits; et; oauto. }
      mDesAll. rename a into tree'. des. rewrite toList_fromList in PURE3.
      subst vret_tgt vret_src. steps_weak.
      deflag.
      eapply IHl.
      - rewrite <- PURE3.
        rewrite <- Hₚ.
        rewrite (app_assoc _ [q] ys).
        eapply Permutation_app_tail.
        rewrite Permutation_app_comm.
        rewrite H.
        eapply (Permutation_app_head [q]).
        rewrite <- H.
        rewrite (Permutation_app_comm [last xs1 0%Z] (tail (removelast xs1))).
        rewrite tail_removelast_last; try lia.
        reflexivity.
      - econs; ss. destruct ys.
        + econs.
        + econs. destruct Hₕ; try discriminate. inversion Etree. subst. lia.
      - assumption.
      - ss.
      - assumption.
      - rewrite <- toList_length.
        erewrite Permutation_length by (symmetry; apply PURE3).
        simpl.
        assert (length (removelast xs1) = l + 1)
          by (rewrite removelast_length; lia).
        rewrite tail_length; lia.
      - red. inversion WF. econs. et.
      - assumption.
    }
    
    i. ss. rewrite unfold_iter_eq. steps.
    rewrite toList_length.
    replace (btsize tree <=? 1) with true
      by (symmetry; eapply leb_correct; lia).
    steps.
    astop. force_l. eexists. steps.
    hret tt; ss.
    iModIntro. iSplit; ss. iPureIntro. esplits; ss.
    - symmetry; assumption.
    - assert (Ht := btsize_eq_1 tree Hₗ).
      destruct Hₕ; try contradiction.
      destruct Ht. subst. simpl.
      econs; try assumption.
      destruct ys.
      + econs.
      + econs. lia.
    Unshelve. et. et.
  Qed.

  Theorem correct : refines2 [Heapsort1.Heapsort] [Heapsort2.Heapsort GlobalStb].
  Proof.
    eapply SimModSem.adequacy_local2; econs; ss.
    i. 
    econstructor 1 with (wf := wf) (le := top2); et; ss; cycle 1.
    { exists tt. red. econs. eapply to_semantic. iIntros. ss. }
    econs; cycle 1.
    econs; cycle 1.
    econs; cycle 1.
    econs.
    - apply sim_heapsort.
    - apply sim_heapify.
    - apply sim_create.
  Qed.

End SIMMODSEM.
