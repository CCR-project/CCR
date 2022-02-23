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
    des. steps.
    astop.
    (* invariant config *) 
    remember (focus btctx_top tree (HeapsortHeader.decode (initial - 1))) as p_init eqn:Eqp.
    destruct p_init as [g t].
    set (tree' := tree) at 2 3 4.
    set (initial' := S (HeapsortHeader.encode (btctx2idx g))).
    assert (Heq : tree = recover_bintree g t).
    { pose proof (recover_focus btctx_top tree (HeapsortHeader.decode (initial - 1))) as R.
      rewrite <- Eqp in R. simpl in R. auto. }
    assert (Hieq : initial = initial').
    { unfold initial'.
      pose proof (btctx2idx_focus tree (HeapsortHeader.decode (initial - 1))) as H.
      rewrite <- Eqp in H. rewrite H. rewrite encode_decode. nia. }
    replace tree' with (recover_bintree g t) by auto.
    replace (toList (recover_bintree g t), initial)
      with (toList (recover_bintree g t), initial').
    2 : { f_equal;try f_equal;auto. }
    clear tree'.
    assert (Hsize : 1<= initial' <= btsize (recover_bintree g t)).
    { rewrite <- Hieq. rewrite <- Heq. nia. }
    assert (statei : initial = initial' \/ initial <> initial').
    { pose proof (Nat.eq_dec initial initial'). destruct H;[left|right];auto. }
    assert (Hi : initial = initial' -> tree = recover_bintree g t) by auto.
    assert (Hcom : complete (recover_bintree g t)) by now rewrite <- Heq;auto.
    assert (completeness : forall t', bteq_shape t t' -> complete (recover_bintree g t')).
    { admit "". }
    assert (permutation : forall t', toList t ≡ₚ toList t'
                                -> toList tree ≡ₚ toList (recover_bintree g t')).
    { admit "". }
    assert (Horder : forall x' x, (match g with
                                    | btctx_top => None
                                    | btctx_left x _ _ | btctx_right x _ _ => Some x
                              end) = Some x'
                             -> initial <> initial'
                             -> option_root t = Some x -> (x' >= x)%Z). { intros. nia. }
    assert (subtree_complete : complete (recover_bintree g t)
             -> (g, t) = focus btctx_top tree (HeapsortHeader.decode (initial' - 1))
             -> complete t). { admit "". }
    rewrite Hieq in Eqp.
    pose proof (subtree_complete Hcom Eqp) as Hsubcom.
    destruct Hsubcom as [n Hsubcom]. clear subtree_complete.
    clear Heq Eqp.
    (* n is not zero *)
    destruct n.
    - inversion Hsubcom;subst.
      assert (contra : initial' > length (toList (recover_bintree g BT_nil))).
      { admit "". }
      assert (H : 1<= initial') by nia.
      rewrite toList_length in contra. nia.
    (* start loop *)
    - steps_weak.
      destruct t as [|x l r] eqn : E;[inversion Hsubcom|].
      remember 0%Z as p. clear Heqp.
      assert (Hheap_ch : initial <> initial' -> heap_pr Z.ge p l /\ heap_pr Z.ge p r /\ (x <= p)%Z) by nia.
      assert (Hheap_nch : forall t', heap_pr Z.ge p t' -> forall j, j >= initial -> heap_at Z.ge (j - 1) (recover_bintree g t')).
      { admit "". }
      clear Hieq.
      assert (stateG : g = btctx_top \/ g <> btctx_top) by now destruct g;[left|right|right];auto.
      deflag.
      revert t x l r g stateG initial' Hi statei E Hcom Hsubcom Hsize completeness permutation Horder Hheap_ch Hheap_nch mrp_src mp_tgt WF ctx mr_src mp_src ACC.
      induction n using Wf_nat.lt_wf_rect;i.
      rewrite unfold_iter_eq. rename H into IHn.
      assert (HT : t <> BT_nil) by now rewrite E;auto.
      pose proof (subtree_nat_Some_node (recover_bintree g t) _ (initial' - 1) HT) as Hsuper.
      clear HT.
      unfold initial' at 1 in Hsuper. simpl minus at 1 in Hsuper.
      unfold subtree_nat in Hsuper.
      rewrite Nat.sub_0_r in Hsuper. rewrite HeapsortHeader.decode_encode in Hsuper.
      pose proof (recover_option_subtree g t) as Ht.
      apply Hsuper in Ht as Hindex. rewrite E in Hindex. clear Hsuper.
      destruct Hindex as [Hindex [Hindex0 Hindex1]].
      replace ((initial' - 1) * 2 + 1) with (initial' * 2 - 1) in Hindex0 by nia.
      replace ((initial' - 1) * 2 + 2) with (initial' * 2) in Hindex1 by nia.
      replace (initial' + (initial' + 0)) with (initial' * 2) by nia.
      rewrite <- E in *.
      destruct (initial' * 2 <=? strings.length (toList (recover_bintree g t)))
               eqn:Ele1;[apply leb_complete in Ele1| apply leb_complete_conv in Ele1].
      all : cycle 1.
      (* terminating case *)
      + steps_weak. rewrite E. force_l. eexists.
        steps_weak. hret tt;ss. iModIntro. iSplit;ss. iPureIntro.
        split;auto. exists (recover_bintree g t). split;rewrite E;auto. split;rewrite <- E;auto.
        specialize (permutation t).
        assert (toList tree ≡ₚ toList (recover_bintree g t)) by auto.
        split;auto.
        assert (none1 : length (toList (recover_bintree g t)) <= initial' * 2 - 1)
          by now unfold initial';nia.
        assert (none2 : length (toList (recover_bintree g t)) <= initial' * 2) by nia.
        apply nth_error_None in none1. apply nth_error_None in none2.
        change (@nth_error Z) with (@HeapsortHeader.lookup Z) in none1.
        change (@nth_error Z) with (@HeapsortHeader.lookup Z) in none2.
        rewrite toList_subtree in none1. rewrite toList_subtree in none2.
        unfold subtree_nat in *. unfold initial' in none1. unfold initial' in none2.
        simpl in none1. simpl in none2.
        rewrite Hindex0 in none1. rewrite Hindex1 in none2.
        destruct l;[|inversion none1]. destruct r;[|inversion none2].
        assert (heap Z.ge (BT_node x BT_nil BT_nil)). { econs;ss;apply heap_nil. }
        
        destruct statei as [statei|statei].
        * intros j H2. apply le_lt_or_eq in H2. destruct H2.
          ** pose proof (Hi statei). rewrite <- H2.
             change (initial < j) with (j > initial) in H1.
             apply PURE3;auto.
          ** replace j with initial' by now rewrite <- H1;rewrite statei. unfold initial'.
             simpl. rewrite Nat.sub_0_r. unfold heap_at. unfold subtree_nat.
             rewrite HeapsortHeader.decode_encode. rewrite recover_option_subtree.
             rewrite E. econs;simpl;auto;apply heap_nil.
        * apply Hheap_nch. rewrite E. econs;simpl;auto;try apply heap_nil.
          apply Hheap_ch in statei. nia.
      (* repeating case *)
      + assert (Htreele1 : 1 <= btsize (recover_bintree g t)) by nia.
        rewrite <- (toList_length (recover_bintree g t)) in Htreele1.
        destruct (length (toList (recover_bintree g t))) as [|m] eqn:Htreele2 in Htreele1
        ;[simpl in Htreele1;inversion Htreele1|].
        clear Htreele1. rewrite Htreele2.
        assert (some0 : initial' * 2 - 1 < length (toList (recover_bintree g t))) by nia.
        apply nth_error_Some in some0.
        change (@nth_error Z) with (@HeapsortHeader.lookup Z) in some0.
        rewrite toList_subtree in some0. unfold subtree_nat in some0.
        rewrite Hindex0 in some0. destruct l as [|xl ll lr];[ss|]. clear some0.
        destruct (initial' * 2 <=? m) eqn:Ele2
        ;[apply leb_complete in Ele2| apply leb_complete_conv in Ele2].
        * assert (some1 : initial' * 2 < length (toList (recover_bintree g t))) by nia.
          apply nth_error_Some in some1.
          change (@nth_error Z) with (@HeapsortHeader.lookup Z) in some1.
          rewrite toList_subtree in some1.
          unfold subtree_nat in some1. rewrite Hindex1 in some1.
          destruct r as [|xr rl rr];[ss|]. clear some1.
          rewrite (toList_subtree (recover_bintree g t) (initial' * 2 - 1)).
          rewrite (toList_subtree (recover_bintree g t) (initial' * 2)).
          unfold subtree_nat in *. rewrite Hindex0. rewrite Hindex1. rewrite Hindex.
          simpl option_root. simpl unwrapU. do 2 rewrite bind_ret_l.
          destruct (xl <? xr)%Z eqn:HZlt
          ;[apply Z.ltb_lt in HZlt|apply Z.ltb_ge in HZlt].
          ** rewrite bind_ret_l.
             rewrite (toList_subtree (recover_bintree g t)
                                     (initial' * 2 + 1 - 1)).
             replace (initial' * 2 + 1 - 1) with (initial' * 2) by nia. unfold subtree_nat.
             rewrite Hindex1. simpl option_root. simpl unwrapU. do 2 rewrite bind_ret_l.
             destruct (xr <=? x)%Z eqn:HZle
             ;[apply Z.leb_le in HZle| apply Z.leb_gt in HZle].
             *** steps_weak. force_l. eexists.
                 steps_weak. hret tt;ss. iModIntro. iSplit; ss. iPureIntro.
                 split;auto. exists (recover_bintree g t). do 2 split;auto.
                 split.
                 { specialize (permutation (BT_node x (BT_node xl ll lr) (BT_node xr rl rr))).
                   rewrite E. apply permutation. rewrite E. auto. }
                 { destruct statei as [statei|statei].
                   - intros. apply le_lt_or_eq in H.
                     destruct H.
                     + pose proof (Hi statei). rewrite <- H0. revert j H. apply PURE3.
                     + rewrite <- H. rewrite statei. unfold initial'.
                       unfold heap_at. unfold subtree_nat. simpl. rewrite Nat.sub_0_r.
                       rewrite HeapsortHeader.decode_encode. rewrite recover_option_subtree.
                       rewrite E. econs;simpl;try nia;auto.
                       * specialize (PURE3 (initial' * 2)). rewrite statei in PURE3.
                         assert (initial' * 2 > initial') by nia.
                         assert (HH : heap_at Z.ge (initial' * 2 - 1) tree) by auto.
                         unfold heap_at in HH. unfold subtree_nat in HH. unfold initial' in HH.
                         simpl in HH. pose proof (Hi statei). rewrite H1 in HH.
                         rewrite Hindex0 in HH. auto.
                       * specialize (PURE3 (S (initial' * 2))). rewrite statei in PURE3.
                         assert (S (initial' * 2) > initial') by nia. simpl in PURE3.
                         assert (HH : heap_at Z.ge (initial' * 2 - 0) tree) by auto.
                         rewrite Nat.sub_0_r in HH.
                         unfold heap_at in HH. unfold subtree_nat in HH. unfold initial' in HH.
                         simpl in HH. pose proof (Hi statei). rewrite H1 in HH.
                         rewrite Hindex1 in HH. auto.
                   - apply Hheap_nch. apply Hheap_ch in statei. rewrite E.
                     destruct statei as [T1 [T2 T3]].
                     econs;simpl;try nia;auto;eapply heap_erase_priority;[apply T1|apply T2]. }
             *** (* steps_weak. *)
        (*          inversion Hsubcom;subst. inversion H_l;subst. *)
        (*          rewrite <- (toList_fromList (swap (toList tree') (initial' * 2) (initial' - 1))). *)
        (*          specialize (IHn n0). assert (J : n0 < S n0) by nia. specialize (IHn J). *)
        (*          specialize (IHn (fromList (swap (toList tree') (initial' * 2) (initial' - 1)))). *)
        (*          assert (length (toList (fromList (swap (toList tree') (initial' * 2) (initial' - 1)))) = length (toList tree')). { admit "". } *)
        (*          rewrite H in IHn. rewrite Htreele2 in IHn. deflag. *)
        (*          eapply IHn. *)
        (*          { intros. unfold heap_at. assert (J1 : j - 1 > initial' * 2) by nia. *)
        (*            assert (J2 : j - 1 > initial' - 1) by nia. assert (J3 : j > initial') by nia. *)
        (*            rewrite (option_subtree_swap tree' _ _ _ J1 J2). *)
        (*            apply Hheap in J3. auto. } *)
        (*          { pose proof (swap_subtree_right tree' (initial' - 1)) as P. *)
        (*            replace ((initial' - 1) * 2 + 2) with (initial' * 2) in P by nia. *)
        (*            rewrite <- Eqp in P. rewrite P. apply completeness. econs;auto. *)
        (*            econs;auto;apply bteq_refl. econs;apply bteq_refl. } *)
        (*          { pose proof (swap_subtree_right tree' (initial' - 1)) as P. *)
        (*            replace ((initial' - 1) * 2 + 2) with (initial' * 2) in P by nia. *)
        (*            rewrite <- Eqp in P. replace (initial' * 2 + 1 - 1) with (initial' * 2) by nia. *)
        (*            rewrite P. *)
        (*            pose proof (focus_recover tree' *)
        (*                                      (BT_node xr (BT_node xl ll lr) (BT_node x rl rr)) *)
        (*                                      (initial' - 1) *)
        (*                                      (initial' * 2)) as PT. *)
        (*            rewrite <- Eqp in PT. *)
        (*            destruct (initial' * 2 =? initial' - 1)%nat eqn: Eqe *)
        (*            ;[apply beq_nat_true in Eqe;nia|]. *)
        (*            destruct (initial' * 2 =? (initial' - 1) * 2 + 1)%nat eqn: Eqe1 *)
        (*            ;[apply beq_nat_true in Eqe1;nia|]. *)
        (*            replace ((initial' - 1) * 2 + 2) with (initial' * 2) in PT by nia. *)
        (*            assert (HH : (initial' * 2 =? initial' * 2)%nat = true) by apply Nat.eqb_refl. *)
        (*            rewrite HH in PT. clear HH. symmetry in PT. apply PT. } *)
        (*          { inversion H_r;subst. *)
        (*            - apply complete_node_perfect_complete;auto. *)
        (*            - apply complete_node_complete_perfect;auto. } *)
        (*          { rewrite <- toList_length. rewrite H. nia.} *)
        (*          { intros. ss. apply completeness. econs;auto;try apply bteq_refl;auto. *)
        (*            eapply bteq_trans. 2:{apply H0.} econs;apply bteq_refl. } *)
        (*          { intros. ss. apply permutation. *)
        (*            do 5 rewrite toList_permutation. rewrite cons_app. *)
        (*            rewrite (cons_app xr). rewrite toList_permutation in H0. *)
        (*            rewrite (cons_app xr ((xl :: toList ll ++ toList lr) ++ toList t')). *)
        (*            rewrite Permutation_app_comm. *)
        (*            rewrite (Permutation_app_comm _ ((xl :: toList ll ++ toList lr) ++ toList t')). *)
        (*            rewrite <- app_assoc. rewrite <- (app_assoc _ (toList t')). *)
        (*            apply Permutation_app_head. rewrite (Permutation_app_comm [xr]). *)
        (*            rewrite Permutation_app_comm. rewrite app_assoc. rewrite <- cons_app. *)
        (*            apply Permutation_app_tail;auto. } *)
        (*          { intros.  simpl in H0. inversion H0;subst. inversion H2;subst. *)
        (*            nia. } *)
        (*          { intros t' HH. apply heap_prop. econs;simpl;auto. nia. *)
        (*            destruct (option_root t') eqn : Ett. simpl.} *)
        (*          { admit "".  } *)
        (*          { admit "".  } *)
        (*          { admit "".  } *)
        (*   ** steps_weak. rewrite (toList_subtree tree' (initial' * 2 - 1)). *)
        (*      unfold subtree_nat. rewrite Hindex0. steps_weak. *)
        (*      destruct (xl <=? x)%Z eqn:HZle *)
        (*      ;[apply Z.leb_le in HZle| apply Z.leb_gt in HZle]. *)
        (*      *** steps_weak. force_l. eexists. *)
        (*          steps_weak. hret tt;ss. iModIntro. iSplit; ss. iPureIntro. *)
        (*          split;auto. exists tree'. do 2 split;auto. *)
        (*          pose proof *)
        (*                 (recover_focus *)
        (*                    btctx_top *)
        (*                    tree' *)
        (*                    (HeapsortHeader.decode (initial' - 1))) as Hrec. *)
        (*          rewrite <- Eqp in Hrec. simpl in Hrec. *)
        (*          split. *)
        (*          { specialize (permutation (BT_node x (BT_node xl ll lr) (BT_node xr rl rr))). *)
        (*            assert *)
        (*              (pem : toList tree ≡ₚ toList *)
        (*                            (recover_bintree g (BT_node x *)
        (*                                                        (BT_node xl ll lr) *)
        (*                                                        (BT_node xr rl rr)))) by auto. *)
        (*            rewrite <- Hrec in pem. et. } *)
        (*          { rewrite Hrec. apply heap_prop. econs;simpl;try nia. *)
        (*            - specialize (Hheap (initial' * 2)). *)
        (*              assert (H : heap_at Z.ge (initial' * 2 - 1) tree') by now apply Hheap;nia. *)
        (*              unfold heap_at in H. unfold subtree_nat in H. rewrite Hindex0 in H. *)
        (*              auto. *)
        (*            - specialize (Hheap (initial' * 2 + 1)). *)
        (*              assert (H : heap_at Z.ge (initial' * 2 + 1 - 1) tree') *)
        (*                by now apply Hheap;nia. *)
        (*              replace (initial' * 2 + 1 - 1) with (initial' * 2) in H by nia. *)
        (*              unfold heap_at in H. unfold subtree_nat in H. rewrite Hindex1 in H. et. } *)
        (*      *** steps_weak. *)
        (*          (* rewrite <- (toList_fromList (swap (toList tree') (initial' * 2 - 1) (initial' - 1))). *) *)
        (*          (* specialize (IHn (fromList (swap (toList tree') (initial' * 2 - 1) (initial' - 1)))). *) *)
        (*          (* assert (length (toList (fromList (swap (toList tree') (initial' * 2 - 1) (initial' - 1)))) = length (toList tree')). { admit "". } *) *)
        (*          (* rewrite H in IHn. rewrite Htreele2 in IHn. deflag. *) *)
        (*          (* eapply IHn;auto. *) *)
        (*          (* **** admit "". *) *)
        (*          (* **** admit "". *) *)
        (*          (* **** admit "". *) *)
        (*          (* **** admit "". *) *)
        (*          (* **** admit "". *) *)
        (*          (* **** admit "". *) *)
        (*          (* **** admit "". *) *)
        (*          (* **** admit "". *) admit "". *)
        (* * steps_weak. *)
        (*   assert (some2 : length (toList tree') <= initial' * 2) by nia. *)
        (*   apply nth_error_None in some2. *)
        (*   change (@nth_error Z) with (@HeapsortHeader.lookup Z) in some2. *)
        (*   rewrite toList_subtree in some2. unfold subtree_nat in some2. *)
        (*   rewrite Hindex1 in some2. destruct r;[|inversion some2]. clear some2. *)
        (*   rewrite (toList_subtree tree' (initial' * 2 - 1)). unfold subtree_nat. *)
        (*   rewrite Hindex0. rewrite Hindex. steps_weak. *)
        (*   destruct (xl <=? x)%Z eqn:HZle *)
        (*   ;[apply Z.leb_le in HZle| apply Z.leb_gt in HZle]. *)
        (*   ** steps_weak. force_l. eexists. *)
        (*      steps_weak. hret tt;ss. iModIntro. iSplit; ss. iPureIntro. *)
        (*      split;auto. exists tree'. do 2 split;auto. *)
        (*      pose proof *)
        (*           (recover_focus *)
        (*              btctx_top *)
        (*              tree' *)
        (*              (HeapsortHeader.decode (initial' - 1))) as Hrec. *)
        (*      rewrite <- Eqp in Hrec. simpl in Hrec. *)
        (*      split. *)
        (*      { specialize (permutation (BT_node x (BT_node xl ll lr) BT_nil)). *)
        (*        assert *)
        (*          (pem : toList tree ≡ₚ toList *)
        (*                        (recover_bintree g (BT_node x *)
        (*                                                    (BT_node xl ll lr) BT_nil))) by auto. *)
        (*        rewrite <- Hrec in pem. et. *)
        (*      } *)
        (*      { rewrite Hrec. apply heap_prop. econs;simpl;try nia. *)
        (*        - specialize (Hheap (initial' * 2)). *)
        (*          assert (H : heap_at Z.ge (initial' * 2 - 1) tree') by now apply Hheap;nia. *)
        (*          unfold heap_at in H. unfold subtree_nat in H. rewrite Hindex0 in H. et. *)
        (*        - specialize (Hheap (initial' * 2 + 1)). *)
        (*          assert (H : heap_at Z.ge (initial' * 2 + 1 - 1) tree') *)
        (*            by now apply Hheap;nia. *)
        (*          replace (initial' * 2 + 1 - 1) with (initial' * 2) in H by nia. *)
        (*          unfold heap_at in H. unfold subtree_nat in H. rewrite Hindex1 in H. et. *)
        (*      } *)
        (*   ** (* steps_weak. *) *)
        (*      (* rewrite <- (toList_fromList (swap (toList tree') (initial' * 2 - 1) (initial' - 1))). *) *)
        (*      (* specialize (IHn (fromList (swap (toList tree') (initial' * 2 - 1) (initial' - 1)))). *) *)
        (*      (* assert (length (toList (fromList (swap (toList tree') (initial' * 2 - 1) (initial' - 1)))) = length (toList tree')). { admit "". } *) *)
        (*      (* rewrite H in IHn. rewrite Htreele2 in IHn. deflag. *) *)
        (*      (* eapply IHn;auto. *) *)
        (*      (* *** admit "". *) *)
        (*      (* *** admit "". *) *)
        (*      (* *** admit "". *) *)
        (*      (* *** admit "". *) *)
        (*      (* *** admit "". *) *)
        (*      (* *** admit "". *) *)
        (*      (* *** admit "". *) *)
        (*      (* *** admit "". *) admit "". *)
        (*      (* leave function *) *)
        (*      Unshelve. et. et. *)
  Admitted.                 

  
  Lemma sim_heapify (sk : alist string Sk.gdef) :
    sim_fnsem wf top2
              ("heapify",
               fun_to_tgt "Heapsort" (GlobalStb sk) {| fsb_fspec := heapify_spec; fsb_body := fun _ => triggerNB |})
              ("heapify", cfunU Heapsort1.heapify_body).
  Proof with lia || eauto.
    Opaque div swap Nat.leb Nat.ltb Z.ltb.
    (** "Entering the function" *)
    init. harg. destruct x as [[tree p] k]. mDesAll; subst.
    clear PURE1. des; subst. steps. astop. steps.
    replace (strings.length (toList tree)) with (btsize tree) by now rewrite toList_length.
    remember (toList tree, 1) as acc_init eqn: H_init. destruct acc_init as [xs i].
    remember (tree) as t eqn: t_init in H_init.
    assert (xs_init : xs = toList t) by congruence. assert (i_init : i = 1) by congruence. clear H_init.
    assert (H_perm : xs ≡ₚ toList (recover_bintree btctx_top t)).
    assert (t_nonempty : t <> BT_nil).
    { rewrite t_init. destruct tree; [inv PURE2 | discriminate]. }

  Admitted.
(** "OLD PROOF"
  Proof with lia || eauto.
    assert (lemma1 : forall (xs : list Z) k, xs <> [] -> upd xs 0 k = k :: list.tail xs) by admit "".
    assert (lemma2 : forall (tree : bintree Z) t i, subtree_nat tree i = Some t -> HeapsortHeader.lookup (toList tree) i = option_root t) by admit "".
    assert (lemma3 : forall (tree : bintree Z) p xs, toList tree ≡ₚ xs -> ((heap Z.ge tree /\ (forall x, In x xs -> Z.ge p x)) <-> heap_pr Z.ge p tree)) by admit "".
    assert (lemma4 : forall (tree : bintree Z) p, heap Z.ge tree -> option_root tree = Some p -> heap_pr Z.ge p tree) by admit "".
    assert (lemma5 : forall (tree : bintree Z), complete tree -> tree = fromList (toList tree)) by admit "".
    assert (lemma8 : forall n : nat, n + 1 - 1 = n) by lia.
    assert (lemma9 : forall (xs : list Z) i1 i2 x1 x2, HeapsortHeader.lookup xs i1 = Some x1 -> upd (upd xs i2 x1) i1 x2 ≡ₚ upd xs i2 x2) by admit "".
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
    { rewrite ds_init. rewrite t_init... }
    assert (H_lookup : forall ds' t', option_subtree ds' t = Some t' -> HeapsortHeader.lookup xs (HeapsortHeader.encode (ds ++ ds')) = option_root t').
    { rewrite ds_init. rewrite xs_init. rewrite t_init. simpl. intros ds' t' H_subtree. apply lemma2. unfold subtree_nat. rewrite HeapsortHeader.decode_encode... }
    assert (H_recover : recover_bintree btctx_top t = fromList xs).
    { rewrite xs_init. rewrite t_init... }
    remember (@btctx_top Z) as g eqn: g_init in H_recover.
    assert (H_bottomup : btctx2idx g = ds).
    { now rewrite g_init; rewrite ds_init. }
    replace (strings.length (toList tree)) with (btsize tree) by now rewrite toList_length.
    (** "Entering the first loop" *)
    clear t_init xs_init ds_init g_init xs_nonempty.
    deflag; revert mrp_src mp_tgt WF ctx mr_src mp_src ACC xs ds g t_nonempty H_permutation H_topdown H_recover H_bottomup H_lookup.
    induction t as [ | x l IH_l r IH_r]; i; [contradiction | rewrite unfold_iter_eq].
    destruct (proj1 (subtree_nat_Some_node tree (BT_node x l r) (HeapsortHeader.encode ds) t_nonempty) H_topdown) as [[H_x [H_l H_r]] [H_left H_right]].
    revert H_left H_right.
    replace (HeapsortHeader.encode ds * 2 + 2) with ((HeapsortHeader.encode ds + 1) * 2) by lia.
    set (obs_if1 := (HeapsortHeader.encode ds + 1) * 2 <=? btsize tree).
    set (obs_if2 := (HeapsortHeader.encode ds + 1) * 2 <? btsize tree).
    intros H_left H_right.
    replace ((HeapsortHeader.encode ds + 1) * 2) with (2 * (HeapsortHeader.encode ds + 1)) by lia.
    replace (HeapsortHeader.lookup xs (2 * (HeapsortHeader.encode ds + 1) - 1)) with (HeapsortHeader.lookup xs (2 * HeapsortHeader.encode ds + 1)) by now f_equal; lia.
    replace (HeapsortHeader.lookup xs (2 * (HeapsortHeader.encode ds + 1))) with (HeapsortHeader.lookup xs (2 * HeapsortHeader.encode ds + 2)) by now f_equal; lia.
    replace (2 * (HeapsortHeader.encode ds + 1) + 1) with ((2 * HeapsortHeader.encode ds + 2) + 1) by lia.
    replace (2 * (HeapsortHeader.encode ds + 1)) with ((2 * HeapsortHeader.encode ds + 1) + 1) by lia.
    replace (HeapsortHeader.encode ds * 2 + 1) with (2 * HeapsortHeader.encode ds + 1) in H_l by lia.
    replace (HeapsortHeader.encode ds * 2 + 2) with (2 * HeapsortHeader.encode ds + 2) in H_r by lia.
    revert H_l H_r.
    replace (2 * HeapsortHeader.encode ds + 1) with (HeapsortHeader.encode (ds ++ [Dir_left])) by exact (HeapsortHeader.encode_last ds Dir_left).
    replace (2 * HeapsortHeader.encode ds + 2) with (HeapsortHeader.encode (ds ++ [Dir_right])) by exact (HeapsortHeader.encode_last ds Dir_right).
    intros H_l H_r.
    assert (H_lookup_l := H_lookup [Dir_left] l Logic.eq_refl).
    assert (H_lookup_r := H_lookup [Dir_right] r Logic.eq_refl).
    rewrite H_lookup_l; rewrite H_lookup_r.
    destruct obs_if1 eqn: H_obs_if1; unfold obs_if1 in H_obs_if1; [apply Nat.leb_le in H_obs_if1 | apply Nat.leb_nle in H_obs_if1]; steps_weak.
    { (** "Iterating the first loop" *)
      destruct (option_root l) as [x_l | ] eqn: H_obs_l; [steps_weak; repeat rewrite lemma8 | destruct l; [contradiction | inv H_obs_l]].
      destruct obs_if2 eqn: H_obs_if2; [apply Nat.ltb_lt in H_obs_if2 | apply Nat.ltb_nlt in H_obs_if2]; steps_weak.
      destruct (option_root r) as [x_r | ] eqn: H_obs_r; [steps_weak; repeat rewrite lemma8 | destruct r; [contradiction | inv H_obs_r]].
      destruct ((x_l <? x_r)%Z) eqn: H_obs_if3; repeat rewrite lemma8; [apply Z.ltb_lt in H_obs_if3; rewrite H_lookup_r | apply Z.ltb_nlt in H_obs_if3; rewrite H_lookup_l]; steps_weak.
      - deflag; eapply IH_r with (g := btctx_right x_r l g)...
        + transitivity (upd xs (HeapsortHeader.encode ds) k)...
        + simpl.
          admit "recover_bintree g (BT_node x_r l r) = fromList (upd xs (HeapsortHeader.encode ds) x_r)".
        + simpl; congruence.
        + intros ds' t' H_subtree.
          rewrite <- (H_lookup ([Dir_right] ++ ds') t' H_subtree).
          rewrite app_assoc.
          admit "HeapsortHeader.lookup (upd xs (HeapsortHeader.encode ds) x_r) (HeapsortHeader.encode ((ds ++ [Dir_right]) ++ ds')) = HeapsortHeader.lookup xs (HeapsortHeader.encode ((ds ++ [Dir_right]) ++ ds'))".
      - deflag; eapply IH_l with (g := btctx_left x_l r g)...
        + transitivity (upd xs (HeapsortHeader.encode ds) k)...
        + simpl.
          admit "recover_bintree g (BT_node x_l l r) = fromList (upd xs (HeapsortHeader.encode ds) x_l)".
        + simpl; congruence.
        + intros ds' t' H_subtree.
          rewrite <- (H_lookup ([Dir_left] ++ ds') t' H_subtree).
          rewrite app_assoc.
          admit "HeapsortHeader.lookup (upd xs (HeapsortHeader.encode ds) x_l) (HeapsortHeader.encode ((ds ++ [Dir_left]) ++ ds')) = HeapsortHeader.lookup xs (HeapsortHeader.encode ((ds ++ [Dir_left]) ++ ds'))".
      - deflag; eapply IH_l with (g := btctx_left x_l r g)...
        + transitivity (upd xs (HeapsortHeader.encode ds) k)...
        + simpl.
          admit "recover_bintree g (BT_node x_l l r) = fromList (upd xs (HeapsortHeader.encode ds) x_l)".
        + simpl; congruence.
        + intros ds' t' H_subtree.
          rewrite <- (H_lookup ([Dir_left] ++ ds') t' H_subtree).
          rewrite app_assoc.
          admit "HeapsortHeader.lookup (upd xs (HeapsortHeader.encode ds) x_l) (HeapsortHeader.encode ((ds ++ [Dir_left]) ++ ds')) = HeapsortHeader.lookup xs (HeapsortHeader.encode ((ds ++ [Dir_left]) ++ ds'))".
    }
    destruct obs_if2 eqn: H_obs_if2; unfold obs_if2 in H_obs_if2; [apply Nat.ltb_lt in H_obs_if2 | apply Nat.ltb_nlt in H_obs_if2]; steps_weak...
    (** "Leaving the first loop" *)
    subst l r. clear IH_l IH_r.
    remember (BT_node x BT_nil BT_nil) as t eqn: t_init.
    (** "Entering the second loop" *)
    clear x H_x H_l H_r t_init obs_if1 obs_if2 H_lookup_l H_lookup_r t_nonempty H_obs_if1 H_obs_if2 H_lookup.
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
*)

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
    eapply heap_pr_if_heap in Hₕ;
      [ | lia | intro Ht; subst; simpl in *; lia ].
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
          eapply removelast_heap; assumption.
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
        rewrite tail_length.
        lia.
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
