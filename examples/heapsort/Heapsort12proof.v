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
    assert (T : forall g i tree, (g, @BT_nil Z) = focus btctx_top tree (HeapsortHeader.decode i)
                            -> complete tree -> i >= length (toList tree)). { admit "". }
    remember (focus btctx_top tree (HeapsortHeader.decode (initial - 1))) as p_init eqn : Eqp.
    destruct p_init as [g t].
    (* assert (completeness : forall t', bteq_shape t' t -> complete (recover_bintree g t')). *)
    (* {admit "".} *)
    (* assert (heap : forall t', heap_pr x t' -> forall j, j >= l -> heap_at j (recover_bintree g t')). *)
    (* {admit "".} *)
    (* assert (permutation : forall t', toList t ≡ₚ toList t' -> toList t ≡ₚ toList (recover_bintree g t')). *)
    (* {admit "".} *)
    pose proof (recover_focus btctx_top tree (HeapsortHeader.decode (initial - 1))) as R_lemma.
    rewrite <- Eqp in R_lemma. simpl in R_lemma. rewrite unfold_iter_eq.
    revert tree initial PURE2 PURE3 PURE4 g R_lemma Eqp mrp_src mp_tgt WF ctx mr_src mp_src ACC.
    induction t;i;
      [apply T in Eqp;auto;rewrite toList_length in Eqp;
       assert (initial <= btsize tree -> False) by nia;destruct PURE3;contradiction|].
    destruct (initial + (initial + 0) <=? strings.length (toList tree)) eqn : E;
      [apply leb_complete in E| apply leb_complete_conv in E].
    - destruct (strings.length (toList tree)) eqn : U;
        [destruct tree;[simpl in PURE3;assert (con : 1<=0) by nia;inversion con|inversion U]| ];
      destruct (initial + (initial + 0) <=? n) eqn : E1;
        [apply leb_complete in E1| apply leb_complete_conv in E1].
      + clear E.
        assert (Pos1 : forall g x t1 t2 initial (tree : bintree Z),
                   (g, BT_node x t1 t2)
                   = focus btctx_top tree (HeapsortHeader.decode (initial - 1))
                   -> HeapsortHeader.lookup (toList tree) (initial * 2 - 1) = option_root t1).
        { admit "". }
        assert (Pos2 : forall g x t1 t2 initial (tree : bintree Z),
                   (g, BT_node x t1 t2)
                   = focus btctx_top tree (HeapsortHeader.decode (initial - 1))
                   -> HeapsortHeader.lookup (toList tree) (initial * 2) = option_root t2).
        { admit "". }
        assert (Pos3 : forall g x t1 t2 initial (tree : bintree Z),
                   (g, BT_node x t1 t2)
                   = focus btctx_top tree (HeapsortHeader.decode (initial - 1))
                   -> HeapsortHeader.lookup (toList tree) (initial - 1) = Some x).
        { admit "". }
        pose proof (Pos3 _ _ _ _ _ _ Eqp) as P3.
        pose proof (Pos1 _ _ _ _ _ _ Eqp) as P1.
        pose proof (Pos2 _ _ _ _ _ _ Eqp) as P2. rewrite P1. rewrite P2.
        assert (complete_t :forall (tree : bintree Z) g x t1 t2 initial, complete tree
                                  -> (g, BT_node x t1 t2)
                                    = focus btctx_top tree
                                            (HeapsortHeader.decode (initial - 1)) 
                                  -> complete (BT_node x t1 t2)).
        { admit "". }
        pose proof (complete_t _ _ _ _ _ _ PURE2 Eqp) as C.
        assert (length_upp : forall (l : list Z) n m, strings.length l = S n
                             -> m <= n
                             -> exists x, HeapsortHeader.lookup l m = Some x).
        { admit "". }
        assert (E11 : initial * 2 <= n) by nia.
        assert (E12 : initial * 2 - 1 <= n) by nia.
        pose proof (length_upp _ _ _ U E11) as some_1.
        pose proof (length_upp _ _ _ U E12) as some_2.
        destruct some_1 as [x1 some_1]. destruct some_2 as [x2 some_2].
        rewrite some_1 in P2. rewrite some_2 in P1. rewrite <- P1. rewrite <- P2.
        steps_weak. destruct (x2 <? x1)%Z eqn : E3
        ;[apply Z.ltb_lt in E3| apply Z.ltb_ge in E3]. 
        * steps_weak. replace (initial * 2 + 1 - 1) with (initial * 2) by nia.
          rewrite some_1. rewrite P3. steps_weak.
          destruct (x1 <=? x)%Z eqn : E4
          ;[apply Z.leb_le in E4| apply Z.leb_gt in E4]. 
          ** steps_weak. force_l. eexists. steps_weak. hret tt; ss.
             iModIntro. iSplit; ss. iPureIntro.
             split;try reflexivity.
             exists tree.
             split;auto. split;auto. split;auto.
             intros. unfold heap_at.
             assert (P5 : forall g t (tree : bintree Z) m,
                        (g, t)
                        = focus btctx_top tree (HeapsortHeader.decode m)
                        -> subtree_nat tree m = Some t).
             { admit "". } apply P5 in Eqp.
             destruct H.
             *** rewrite Eqp.
                 (* surrender : i need heap t1 heap t2 option_root t1 = x1 brr... *)
             
        
  Admitted.

  Lemma sim_heapify (sk : alist string Sk.gdef) :
    sim_fnsem wf top2
              ("heapify",
               fun_to_tgt "Heapsort" (GlobalStb sk) {| fsb_fspec := heapify_spec; fsb_body := fun _ => triggerNB |})
              ("heapify", cfunU Heapsort1.heapify_body).
  Proof with lia || eauto.
    assert (lemma1 : forall (xs : list Z) k, xs <> [] -> upd xs 0 k = k :: list.tail xs) by admit "".
    assert (lemma2 : forall (tree : bintree Z) t i, subtree_nat tree i = Some t -> HeapsortHeader.lookup (toList tree) i = option_root t) by admit "".
    assert (lemma3 : forall (tree : bintree Z) p xs, toList tree ≡ₚ xs -> ((heap Z.ge tree /\ (forall x, In x xs -> Z.ge p x)) <-> heap_pr Z.ge p tree)) by admit "".
    assert (lemma4 : forall (tree : bintree Z) p, heap Z.ge tree -> option_root tree = Some p -> heap_pr Z.ge p tree) by admit "".
    assert (lemma5 : forall (tree : bintree Z), complete tree -> tree = fromList (toList tree)) by admit "".
    assert (lemma6 : forall (tree : bintree Z), btsize tree = strings.length (toList tree)) by admit "".
    assert (lemma7 : forall (tree : bintree Z) i t,
      t <> BT_nil ->
      subtree_nat tree i = Some t ->
      match t with
      | BT_nil => False
      | BT_node x l r =>
        (HeapsortHeader.lookup (toList tree) i = Some x /\ subtree_nat tree (i * 2 + 1) = Some l /\ subtree_nat tree (i * 2 + 2) = Some r)
        /\ (if i * 2 + 2 <=? btsize tree then l <> BT_nil else l = BT_nil)
        /\ (if i * 2 + 2 <? btsize tree then r <> BT_nil else r = BT_nil)
      end
    ) by admit "".
    assert (lemma8 : forall n : nat, n + 1 - 1 = n) by lia.
    assert (lemma9 : forall (xs : list Z) i1 i2 x1 x2, HeapsortHeader.lookup xs i1 = Some x1 -> upd (upd xs i2 x1) i1 x2 ≡ₚ upd xs i2 x2) by admit "".
    set (btctx2idx :=
      fix btctx2idx_fix (g : btctx Z) : list dir_t :=
      match g with
      | btctx_top => []
      | btctx_left _ _ g => btctx2idx_fix g ++ [Dir_left]
      | btctx_right _ _ g => btctx2idx_fix g ++ [Dir_right]
      end
    ).
    set (upd_root := fun k (t : bintree Z) =>
      match t with
      | BT_nil => BT_nil
      | BT_node x l r => BT_node k l r
      end
    ).
    assert (claim_upd_xs_0_k : forall (xs : list Z) k, (upd xs 0 k) = (toList (upd_root k (fromList xs)))) by admit "".
    assert (claim_encode_last : forall ds d, HeapsortHeader.encode (ds ++ [d]) > 0) by admit "".
    Opaque div swap Nat.leb Nat.ltb Z.ltb.
    (** "Entering the function" *)
    init. harg. destruct x as [[tree p] k]. mDesAll; subst.
    clear PURE1. des; subst. steps. astop. steps.
    (** "Invariants" *)
    remember (toList tree, 1) as acc_init eqn: H_init. destruct acc_init as [xs i].
    remember (tree) as t eqn: t_init in H_init.
    assert (xs_init : xs = toList t) by congruence.
    assert (i_init : i = 1) by congruence.
    clear H_init.
    assert (t_nonempty : t <> BT_nil).
    { rewrite t_init. destruct tree; [inv PURE2 | discriminate]. }
    assert (xs_nonempty : xs <> []).
    { rewrite xs_init. now destruct t. }
    assert (ds_init_aux1 : i = HeapsortHeader.encode [] + 1) by now rewrite i_init.
    remember (@nil dir_t) as ds eqn: ds_init in ds_init_aux1. clear i_init; subst i.
    assert (H_permutation : upd xs (HeapsortHeader.encode ds) k ≡ₚ k :: list.tail (toList tree)).
    { rewrite ds_init. rewrite <- t_init. rewrite <- xs_init. simpl. now rewrite lemma1. }
    assert (H_topdown : subtree_nat tree (HeapsortHeader.encode ds) = Some t).
    { rewrite ds_init. simpl. rewrite t_init... }
    assert (H_lookup : forall ds' t', option_subtree ds' t = Some t' -> HeapsortHeader.lookup xs (HeapsortHeader.encode (ds ++ ds')) = option_root t').
    { rewrite ds_init. rewrite xs_init. rewrite t_init. simpl. intros ds' t' H_subtree. apply lemma2. unfold subtree_nat. rewrite HeapsortHeader.decode_encode... }
    assert (H_recover : recover_bintree btctx_top t = fromList xs).
    { rewrite xs_init. rewrite t_init. simpl... }
    remember (btctx_top) as g eqn: g_init in H_recover.
    assert (H_bottomup : btctx2idx g = ds).
    { now rewrite g_init; rewrite ds_init. }
    replace (strings.length (toList tree)) with (btsize tree) by apply lemma6.
    (** "Entering the first loop" *)
    clear t_init xs_init ds_init g_init xs_nonempty.
    deflag; revert mrp_src mp_tgt WF ctx mr_src mp_src ACC xs ds g t_nonempty H_permutation H_topdown H_recover H_bottomup H_lookup.
    induction t as [ | x l IH_l r IH_r]; i; [contradiction | rewrite unfold_iter_eq].
    destruct (lemma7 tree (HeapsortHeader.encode ds) (BT_node x l r) t_nonempty H_topdown) as [[H_x [H_left H_right]] [H_l H_r]].
    revert H_l H_r. replace (HeapsortHeader.encode ds * 2 + 2) with ((HeapsortHeader.encode ds + 1) * 2) by lia.
    set (obs_if1 := (HeapsortHeader.encode ds + 1) * 2 <=? btsize tree).
    set (obs_if2 := (HeapsortHeader.encode ds + 1) * 2 <? btsize tree).
    intros H_l H_r.
    replace ((HeapsortHeader.encode ds + 1) * 2) with (2 * (HeapsortHeader.encode ds + 1)) by lia.
    replace (HeapsortHeader.lookup xs (2 * (HeapsortHeader.encode ds + 1) - 1)) with (HeapsortHeader.lookup xs (2 * HeapsortHeader.encode ds + 1)) by now f_equal; lia.
    replace (HeapsortHeader.lookup xs (2 * (HeapsortHeader.encode ds + 1))) with (HeapsortHeader.lookup xs (2 * HeapsortHeader.encode ds + 2)) by now f_equal; lia.
    replace (2 * (HeapsortHeader.encode ds + 1) + 1) with ((2 * HeapsortHeader.encode ds + 2) + 1) by lia.
    replace (2 * (HeapsortHeader.encode ds + 1)) with ((2 * HeapsortHeader.encode ds + 1) + 1) by lia.
    replace (HeapsortHeader.encode ds * 2 + 1) with (2 * HeapsortHeader.encode ds + 1) in H_left by lia.
    replace (HeapsortHeader.encode ds * 2 + 2) with (2 * HeapsortHeader.encode ds + 2) in H_right by lia.
    revert H_left H_right.
    replace (2 * HeapsortHeader.encode ds + 1) with (HeapsortHeader.encode (ds ++ [Dir_left])) by exact (HeapsortHeader.encode_last ds Dir_left).
    replace (2 * HeapsortHeader.encode ds + 2) with (HeapsortHeader.encode (ds ++ [Dir_right])) by exact (HeapsortHeader.encode_last ds Dir_right).
    intros H_left H_right.
    assert (H_lookup_l := H_lookup [Dir_left] l Logic.eq_refl).
    assert (H_lookup_r := H_lookup [Dir_right] r Logic.eq_refl).
    rewrite H_lookup_l. rewrite H_lookup_r.
    destruct obs_if1 eqn: H_obs_if1; unfold obs_if1 in H_obs_if1; [apply Nat.leb_le in H_obs_if1 | apply Nat.leb_nle in H_obs_if1]; steps_weak.
    { (** "Iterating the first loop" *)
      destruct (option_root l) as [x_l | ] eqn: H_obs_l; [steps_weak | destruct l; [contradiction | inv H_obs_l]].
      destruct obs_if2 eqn: H_obs_if2.
      destruct (option_root r) as [x_r | ] eqn: H_obs_r; [steps_weak | destruct r; [contradiction | inv H_obs_r]].
      destruct ((x_l <? x_r)%Z) eqn: H_obs_if3; steps_weak.
      - repeat rewrite lemma8; (try rewrite H_lookup_r); steps_weak.
        deflag; eapply IH_r with (g := btctx_right x_r l g)...
        + transitivity (upd xs (HeapsortHeader.encode ds) k)...
        + simpl.
          admit "recover_bintree g (BT_node x_r l r) = fromList (upd xs (HeapsortHeader.encode ds) x_r)".
        + simpl. congruence.
        + intros ds' t' H_subtree.
          rewrite <- (H_lookup ([Dir_right] ++ ds') t' H_subtree).
          rewrite app_assoc.
          admit "HeapsortHeader.lookup (upd xs (HeapsortHeader.encode ds) x_r) (HeapsortHeader.encode ((ds ++ [Dir_right]) ++ ds')) = HeapsortHeader.lookup xs (HeapsortHeader.encode ((ds ++ [Dir_right]) ++ ds'))".
      - repeat rewrite lemma8; (try rewrite H_lookup_l); steps_weak.
        deflag; eapply IH_l with (g := btctx_left x_l r g)...
        + transitivity (upd xs (HeapsortHeader.encode ds) k)...
        + simpl.
          admit "recover_bintree g (BT_node x_l l r) = fromList (upd xs (HeapsortHeader.encode ds) x_l)".
        + simpl. congruence.
        + intros ds' t' H_subtree.
          rewrite <- (H_lookup ([Dir_left] ++ ds') t' H_subtree).
          rewrite app_assoc.
          admit "HeapsortHeader.lookup (upd xs (HeapsortHeader.encode ds) x_l) (HeapsortHeader.encode ((ds ++ [Dir_left]) ++ ds')) = HeapsortHeader.lookup xs (HeapsortHeader.encode ((ds ++ [Dir_left]) ++ ds'))".
      - repeat rewrite lemma8; (try rewrite H_lookup_l); steps_weak.
        deflag; eapply IH_l with (g := btctx_left x_l r g)...
        + transitivity (upd xs (HeapsortHeader.encode ds) k)...
        + simpl.
          admit "recover_bintree g (BT_node x_l l r) = fromList (upd xs (HeapsortHeader.encode ds) x_l)".
        + simpl. congruence.
        + intros ds' t' H_subtree.
          rewrite <- (H_lookup ([Dir_left] ++ ds') t' H_subtree).
          rewrite app_assoc.
          admit "HeapsortHeader.lookup (upd xs (HeapsortHeader.encode ds) x_l) (HeapsortHeader.encode ((ds ++ [Dir_left]) ++ ds')) = HeapsortHeader.lookup xs (HeapsortHeader.encode ((ds ++ [Dir_left]) ++ ds'))".
    }
    destruct obs_if2 eqn: H_obs_if2; unfold obs_if2 in H_obs_if2; [apply Nat.ltb_lt in H_obs_if2 | apply Nat.ltb_nlt in H_obs_if2]; steps_weak.
    { lia. }
    (** "Leaving the first loop" *)
    subst l r. clear IH_l IH_r.
    remember (BT_node x BT_nil BT_nil) as t eqn: t_init.
    (** "Entering the second loop" *)
    clear x H_x H_left H_right t_init obs_if1 obs_if2 H_lookup_l H_lookup_r t_nonempty H_obs_if1 H_obs_if2 H_lookup.
    deflag; revert mrp_src mp_tgt WF ctx mr_src mp_src ACC xs ds t H_permutation H_topdown H_recover H_bottomup.
    induction g as [ | x r g IH | x l g IH]; i; rewrite unfold_iter_eq.
    { (** "Leaving the second loop" *)
      simpl in H_bottomup; subst ds. simpl in *.
      steps_weak. force_l. eexists. steps_weak. hret tt; ss.
      iModIntro. iSplit; ss. iPureIntro.
      split; try reflexivity.
      exists (upd_root k t); splits.
      - rewrite H_recover. f_equal...
      - rewrite H_recover.
        destruct (complete_fromList xs) as [rk H_complete'].
        eexists. inv H_complete'; simpl.
        + econs 1...
        + econs 2...
        + econs 3...
      - transitivity (upd xs 0 k).
        + symmetry. exact H_permutation.
        + rewrite H_recover. rewrite claim_upd_xs_0_k...
      - admit "(heap_pr Z.ge p (upd_root k t))".
    }
    (** "Iterating the second loop" *)
    - simpl in H_bottomup; subst ds.
      set (i := HeapsortHeader.encode (btctx2idx g ++ [Dir_left]) + 1).
      destruct (Nat.eqb i 1) eqn: H_obs_if1; [apply Nat.eqb_eq in H_obs_if1 | apply Nat.eqb_neq in H_obs_if1].
      { pose (claim_encode_last (btctx2idx g) Dir_left). unfold i in H_obs_if1... }
      assert (H_par_i : i `div` 2 = HeapsortHeader.encode (btctx2idx g) + 1) by admit "".
      assert (H_parent : HeapsortHeader.lookup xs (HeapsortHeader.encode (btctx2idx g)) = Some x) by admit "".
      rewrite H_par_i; rewrite lemma8; rewrite H_parent; steps_weak.
      destruct ((k <? x)%Z) eqn: H_obs_if2; steps_weak.
      { (** "Leaving the second loop" *)
        force_l. eexists. steps_weak. hret tt; ss.
        iModIntro. iSplit; ss. iPureIntro.
        split; try reflexivity.
        exists (fromList (upd xs (HeapsortHeader.encode (btctx2idx g ++ [Dir_left])) k)); splits.
        - rewrite toList_fromList. unfold i. now rewrite lemma8.
        - apply complete_fromList.
        - now rewrite toList_fromList.
        - admit "heap_pr Z.ge p (fromList (upd xs (HeapsortHeader.encode (btctx2idx g ++ [Dir_left])) k))".
      }
      deflag; eapply IH with (t := BT_node x r t)...
      + transitivity (upd xs (HeapsortHeader.encode (btctx2idx g ++ [Dir_left])) k)...
        replace ((HeapsortHeader.encode (btctx2idx g ++ [Dir_left]))) with (i - 1) by lia.
        apply (lemma9 xs (HeapsortHeader.encode (btctx2idx g)) (i - 1) x k)...
      + admit "subtree_nat tree (HeapsortHeader.encode (btctx2idx g)) = Some (BT_node x r t)".
      + unfold i. rewrite lemma8.
        admit "recover_bintree g (BT_node x r t) = fromList (upd xs (HeapsortHeader.encode (btctx2idx g ++ [Dir_left])) x)".
    - simpl in H_bottomup; subst ds.
      set (i := HeapsortHeader.encode (btctx2idx g ++ [Dir_right]) + 1).
      destruct (Nat.eqb i 1) eqn: H_obs_if1; [apply Nat.eqb_eq in H_obs_if1 | apply Nat.eqb_neq in H_obs_if1].
      { pose (claim_encode_last (btctx2idx g) Dir_right). unfold i in H_obs_if1... }
      assert (H_par_i : i `div` 2 = HeapsortHeader.encode (btctx2idx g) + 1) by admit "".
      assert (H_parent : HeapsortHeader.lookup xs (HeapsortHeader.encode (btctx2idx g)) = Some x) by admit "".
      rewrite H_par_i; rewrite lemma8; rewrite H_parent; steps_weak.
      destruct ((k <? x)%Z) eqn: H_obs_if2; steps_weak.
      { (** "Leaving the second loop" *)
        force_l. eexists. steps_weak. hret tt; ss.
        iModIntro. iSplit; ss. iPureIntro.
        split; try reflexivity.
        exists (fromList (upd xs (HeapsortHeader.encode (btctx2idx g ++ [Dir_right])) k)); splits.
        - rewrite toList_fromList. unfold i. now rewrite lemma8.
        - apply complete_fromList.
        - now rewrite toList_fromList.
        - admit "heap_pr Z.ge p (fromList (upd xs (HeapsortHeader.encode (btctx2idx g ++ [Dir_right])) k))".
      }
      deflag; eapply IH with (t := BT_node x l t)...
      + transitivity (upd xs (HeapsortHeader.encode (btctx2idx g ++ [Dir_right])) k)...
        replace ((HeapsortHeader.encode (btctx2idx g ++ [Dir_right]))) with (i - 1) by lia.
        apply (lemma9 xs (HeapsortHeader.encode (btctx2idx g)) (i - 1) x k)...
      + admit "subtree_nat tree (HeapsortHeader.encode (btctx2idx g)) = Some (BT_node x r t)".
      + unfold i. rewrite lemma8.
        admit "recover_bintree g (BT_node x l t) = fromList (upd xs (HeapsortHeader.encode (btctx2idx g ++ [Dir_right])) x)".
    (** "Leaving the function" *)
    Unshelve.
  Qed.

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
