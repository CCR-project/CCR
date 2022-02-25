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
Require Import HeapsortProperties.
Require Import Heapsort1 Heapsort2.
Require Import HTactics ProofMode.
Require Import SimModSem.
Require Import Coq.Sorting.Sorted.

Set Implicit Arguments.

Tactic Notation "repl" constr(e) "with" constr(e') "at" ne_integer_list(n) :=
  let x := fresh in
  set e as x at n;
  replace x with e';
  subst x.

Tactic Notation "repl" constr(e) "with" constr(e') "at" ne_integer_list(n) "by" tactic(tac) :=
  let x := fresh in
  set e as x at n;
  replace x with e' by tac;
  subst x.

Ltac steps_weak := repeat (prep; try _step; simpl).
Ltac monad_law := repeat first [ rewrite bind_ret_l | rewrite bind_ret_r | rewrite bind_bind ].

Lemma unfold_iter_eq:
  ∀ (E : Type → Type) (A B : Type) (f : A → itree E (A + B)) (x : A),
    ITree.iter f x = ` lr : A + B <- f x;; match lr with
                                          | inl l => tau;; ITree.iter f l
                                          | inr r => Ret r
                                          end.
Proof. intros. eapply bisim_is_eq. eapply unfold_iter. Qed.

Lemma iter_if_Ret (E : Type -> Type) (A : Type) (x y : A) (b : bool) :
  (if b then go (@RetF E A _ x) else Ret y) = (Ret (if b then x else y)).
Proof.
  destruct b; reflexivity.
Qed.

Ltac solve_heap H :=
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  destruct H as [H1 [H2 H3]];
  splits; try lia;
  inversion H1; inversion H2; subst;
  match goal with
  | [ |- heap_pr _ _ ?t ] => destruct t; [ eapply heap_pr_nil | ]
  end;
  match goal with
  | [ H : heap _ ?t |- heap_pr _ _ ?t ] => inversion H; eapply heap_pr_node; auto
  end.

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
    remember (focus btctx_top tree (decodeIdx (initial - 1))) as p_init eqn:Eqp.
    destruct p_init as [g t].
    set (initial' := S (encodeIdx (btctx2idx g))).
    assert (Heq : tree = recover_bintree g t).
    { pose proof (recover_focus btctx_top tree (decodeIdx (initial - 1))) as R.
      rewrite <- Eqp in R. simpl in R. auto. }
    assert (Hieq : initial = initial').
    { unfold initial'.
      pose proof (btctx2idx_focus tree (decodeIdx (initial - 1))) as H.
      rewrite <- Eqp in H. rewrite H. rewrite encode_decode. nia. }
    repl tree with (recover_bintree g t) at 4 by auto.
    replace (length (toList tree)) with (btsize tree) by (symmetry; eapply toList_length).
    repl initial with initial' at 2 by (f_equal; try f_equal; auto).
    assert (Hsize : 1<= initial' <= btsize (recover_bintree g t)).
    { rewrite <- Hieq. rewrite <- Heq. nia. }
    assert (Hcom : complete (recover_bintree g t)) by now rewrite <- Heq;auto.
    assert (permutation : toList tree ≡ₚ toList (recover_bintree g t)).
    { admit "". }
    rewrite Hieq in Eqp.
    assert (Hsubcom : complete t) by (eapply recover_complete; eassumption).
    destruct Hsubcom as [n Hsubcom].
    clear Heq Eqp.
    (* n is not zero *)
    destruct n.
    { inversion Hsubcom;subst.
      assert (contra : initial' > length (toList (recover_bintree g BT_nil))).
      { admit "". }
      assert (H : 1<= initial') by nia.
      rewrite toList_length in contra. nia. }
    (* start loop *)
    steps_weak.
    destruct t as [|x l r] eqn : E;[inversion Hsubcom|].
    remember 0%Z as p. (* TODO : set p as max value of x, l, r *)
    assert (Hheap_ch : heap_pr Z.ge p l /\ heap_pr Z.ge p r /\ (x <= p)%Z) by admit "".
    assert (Hheap_nch : forall t', heap_pr Z.ge p t' -> forall j, j >= initial -> heap_at Z.ge (j - 1) (recover_bintree g t')).
    { admit "". }
    clear Heqp.
    clear Hieq.
    deflag.
    revert p t x l r g initial' E Hcom Hsubcom Hsize permutation Hheap_ch Hheap_nch mrp_src mp_tgt WF ctx mr_src mp_src ACC.
    induction n as [n IHn] using Wf_nat.lt_wf_rect;i. rewrite unfold_iter_eq.
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
    destruct (initial' * 2 <=? btsize tree)
             eqn:Ele1;[apply leb_complete in Ele1| apply leb_complete_conv in Ele1].
    all : cycle 1.
    - (* has no child *)
      steps_weak. rewrite E. force_l. eexists.
      steps_weak. hret tt;ss. iModIntro. iSplit;ss. iPureIntro.
      split;auto. exists (recover_bintree g t). split;rewrite E;auto. split;rewrite <- E;auto.
      split;auto.
      replace (S (S (encodeIdx (btctx2idx g) * 2))) with (initial' * 2) in Ele1 by lia.
      assert (Hinitial' : initial' > btsize (recover_bintree g t) / 2).
      { rewrite <- toList_length.
        rewrite <- (Permutation_length permutation).
        rewrite toList_length.
        apply Nat.div_lt_upper_bound; try lia.
      }
      pose proof (subtree_nat_leaf (recover_bintree g t) Hcom initial' Hinitial') as H.
      unfold subtree_nat in H. replace (initial' - 1) with (encodeIdx (btctx2idx g)) in H by lia.
      rewrite HeapsortHeader.decode_encode in H. rewrite Ht in H.
      rewrite E in H. inv H.
      apply Hheap_nch. econs; simpl; auto; try apply heap_nil. lia.
    - (* has 1 or 2 child *)
      (* TODO : remove Hts *)
      assert (Hts : btsize tree = length (toList (recover_bintree g t)))
        by (rewrite <- (Permutation_length permutation); symmetry; eapply toList_length).
      rewrite Hts in Ele1.
      assert (Htreele1 : 1 <= btsize (recover_bintree g t)) by nia.
      rewrite <- (toList_length (recover_bintree g t)) in Htreele1.
      destruct (length (toList (recover_bintree g t))) as [|m] eqn:Htreele2 in Htreele1
      ;[simpl in Htreele1;inversion Htreele1|].
      clear Htreele1.
      repl (btsize tree) with (S m) at 3 by (transitivity (length (toList (recover_bintree g t))); auto).
      assert (some0 : initial' * 2 - 1 < length (toList (recover_bintree g t))) by nia.
      apply nth_error_Some in some0.
      rewrite toList_subtree in some0. unfold subtree_nat in some0.
      rewrite Hindex0 in some0. destruct l as [|xl ll lr];[ss|]. clear some0.
      destruct (initial' * 2 <=? m) eqn:Ele2
      ;[apply leb_complete in Ele2| apply leb_complete_conv in Ele2].
      + (* has 2 child *)
        assert (some1 : initial' * 2 < length (toList (recover_bintree g t))) by nia.
        apply nth_error_Some in some1.
        rewrite toList_subtree in some1.
        unfold subtree_nat in some1. rewrite Hindex1 in some1.
        destruct r as [|xr rl rr];[ss|]. clear some1.
        rewrite (toList_subtree (recover_bintree g t) (initial' * 2 - 1)).
        rewrite (toList_subtree (recover_bintree g t) (initial' * 2)).
        unfold subtree_nat in *. rewrite Hindex0. rewrite Hindex1. rewrite Hindex.
        simpl option_root. simpl unwrapU.
        monad_law. rewrite iter_if_Ret. monad_law.
        replace (nth_error (toList (recover_bintree g t))
                           ((if (xl <? xr)%Z
                             then initial' * 2 + 1
                             else initial' * 2) - 1))
          with (Some (Z.max xl xr)).
        2: {
          destruct (xl <? xr)%Z eqn: HZlt; [ apply Z.ltb_lt in HZlt | apply Z.ltb_ge in HZlt ].
          - replace (xl `max` xr)%Z with xr by lia.
            replace (initial' * 2 + 1 - 1) with (initial' * 2) by lia.
            rewrite toList_subtree. unfold subtree_nat. rewrite Hindex1. reflexivity.
          - replace (xl `max` xr)%Z with xl by lia.
            rewrite toList_subtree. unfold subtree_nat. rewrite Hindex0. reflexivity.
        }
        simpl unwrapU. monad_law.
        destruct (xl `max` xr <=? x)%Z eqn:HZlt; [apply Z.leb_le in HZlt | apply Z.leb_gt in HZlt ].
        { steps_weak. force_l. eexists.
          steps_weak. hret tt; ss. iModIntro. iSplit; ss. iPureIntro.
          split; auto. exists (recover_bintree g t). splits; auto.
          apply Hheap_nch. rewrite E.
          des. econs; simpl; try lia; auto; eapply heap_erase_priority; eauto.
        }
        monad_law. rewrite bind_tau. force_r.
        rewrite <- (toList_fromList (swap (toList (recover_bintree g t)) _ _)).
        replace (fromList (swap (toList (recover_bintree g t))
                                ((if (xl <? xr)%Z then initial' * 2 + 1 else initial' * 2) - 1)
                                (initial' - 1)))
          with (if (xl <? xr)%Z
                then recover_bintree g (BT_node xr (BT_node xl ll lr) (BT_node x rl rr))
                else recover_bintree g (BT_node xl (BT_node x ll lr) (BT_node xr rl rr))
               ) by admit "swap".
        unfold initial'.
        rewrite E in Hsubcom. destruct n; [ inversion Hsubcom; inversion H_l |].
        destruct (xl <? xr)%Z eqn:HZlt'
        ;[apply Z.ltb_lt in HZlt'|apply Z.ltb_ge in HZlt'].
        * (* deal with right child *)
          replace (S (encodeIdx (btctx2idx g)) * 2 + 1) with
            (S (encodeIdx (btctx2idx (btctx_right xr (BT_node xl ll lr) g)))).
          2 :{ simpl. rewrite encode_last. nia. }
          replace (toList (recover_bintree g (BT_node xr (BT_node xl ll lr) (BT_node x rl rr))))
            with (toList (recover_bintree
                            (btctx_right xr (BT_node xl ll lr) g)
                            (BT_node x rl rr))) by auto.
          inversion Hsubcom.
          { deflag. eapply (IHn n); ss; et.
            - intros. ss. eapply (equicomplete_thm g t). rewrite E.
              econs;auto;try apply bteq_refl;auto. econs;apply bteq_refl. assumption.
            - inversion H_r. 
              + eapply complete_node_perfect_complete;eauto.
              + eapply complete_node_complete_perfect;eauto.
            - rewrite encode_last. rewrite <- toList_length. rewrite E in Htreele2.
              split;try nia. admit "".
            - intros. ss. rewrite permutation. rewrite E. admit "".
            - instantiate (1 := xr). solve_heap Hheap_ch.
            - intros t' HH j Hj.
              apply Hheap_nch;auto.
              destruct Hheap_ch as [H' [H'' X]]. inversion H'. inversion H''. inversion HH.
              + econs;simpl;auto;try nia. eapply heap_erase_priority;eauto. apply heap_nil.
              + econs;simpl;auto;try nia;econs;simpl;auto;try nia.
          }
          { destruct n; [ inversion H_r |].
            deflag. eapply (IHn n); ss; et.
            - intros. ss. apply (equicomplete_thm g t). rewrite E.
              econs;auto;try apply bteq_refl;auto. econs;apply bteq_refl. assumption.
            - inversion H_r.
              eapply complete_node_perfect_complete; eauto; apply perfect'2complete'; auto.
            - rewrite encode_last. rewrite <- toList_length. rewrite E in Htreele2.
              split;try nia. admit "".
            - intros. ss. rewrite permutation. rewrite E. admit "".
            - instantiate (1 := xr). solve_heap Hheap_ch.
            - intros t' HH j Hj.
              apply Hheap_nch;auto.
              destruct Hheap_ch as [H' [H'' X]]. inversion H'. inversion H''. inversion HH.
              + econs;simpl;auto;try nia. eapply heap_erase_priority;eauto. apply heap_nil.
              + econs;simpl;auto;try nia;econs;simpl;auto;try nia.
          }
        * (* deal with left child *)
          replace (S (encodeIdx (btctx2idx g)) * 2) with
            (S (encodeIdx (btctx2idx (btctx_left xl (BT_node xr rl rr) g)))).
          2 :{ simpl. rewrite encode_last. nia. }
          replace (toList (recover_bintree g (BT_node xl (BT_node x ll lr) (BT_node xr rl rr))))
            with (toList (recover_bintree
                            (btctx_left xl (BT_node xr rl rr) g)
                            (BT_node x ll lr))) by auto.
          inversion Hsubcom.
          { deflag. eapply (IHn n); ss; et.
            - intros. ss. apply (equicomplete_thm g t). rewrite E.
              econs;auto;try apply bteq_refl;auto. econs;apply bteq_refl. assumption.
            - inversion H_l.
              eapply complete_node_perfect_complete;eauto.
              apply perfect'2complete';auto.
            - rewrite encode_last. rewrite <- toList_length. rewrite E in Htreele2.
              split;try nia. admit "".
            - intros. ss. rewrite permutation. rewrite E. admit "".
            - instantiate (1 := xl). solve_heap Hheap_ch.
            - intros t' HH j Hj.
              apply Hheap_nch;auto.
              destruct Hheap_ch as [H' [H'' X]]. inversion H'. inversion H''. inversion HH.
              + econs;simpl;auto;try nia. all : cycle 1.
                eapply heap_erase_priority;eauto. apply heap_nil.
              + econs;simpl;auto;try nia;econs;simpl;auto;try nia.
          }
          { deflag. eapply (IHn n); ss; et.
            - intros. ss. apply (equicomplete_thm g t). rewrite E.
              econs;auto;try apply bteq_refl;auto. econs;apply bteq_refl. assumption.
            - inversion H_l.
              + eapply complete_node_perfect_complete;eauto.
              + eapply complete_node_complete_perfect;eauto.
            - rewrite encode_last. rewrite <- toList_length. rewrite E in Htreele2.
              split;try nia. admit "".
            - intros. ss. rewrite permutation. rewrite E. admit "".
            - instantiate (1 := xl). solve_heap Hheap_ch.
            - intros t' HH j Hj.
              apply Hheap_nch;auto.
              destruct Hheap_ch as [H' [H'' X]]. inversion H'. inversion H''. inversion HH.
              + econs;simpl;auto;try nia. all : cycle 1.
                eapply heap_erase_priority;eauto. apply heap_nil.
              + econs;simpl;auto;try nia;econs;simpl;auto;try nia.
          }
      + (* has 1 child *)
        monad_law.
        assert (some2 : length (toList (recover_bintree g t)) <= initial' * 2) by nia.
        apply nth_error_None in some2.
        rewrite toList_subtree in some2. unfold subtree_nat in some2.
        rewrite Hindex1 in some2. destruct r;[|inversion some2]. clear some2.
        rewrite (toList_subtree (recover_bintree g t) (initial' * 2 - 1)). unfold subtree_nat.
        rewrite Hindex0. rewrite Hindex. simpl option_root. simpl unwrapU. monad_law.
        destruct (xl <=? x)%Z eqn:HZle
        ;[apply Z.leb_le in HZle| apply Z.leb_gt in HZle].
        ** steps_weak. force_l. eexists.
           steps_weak. hret tt;ss. iModIntro. iSplit; ss. iPureIntro.
           split;auto. exists (recover_bintree g t). splits; auto.
           apply Hheap_nch. rewrite E.
           destruct Hheap_ch as [T1 [T2 T3]].
           econs;simpl;try nia;auto;eapply heap_erase_priority;[apply T1|apply T2].
        ** monad_law. rewrite bind_tau. force_r.
           rewrite <- (toList_fromList (swap (toList (recover_bintree g t)) (initial' * 2 - 1) (initial' - 1))).
           rewrite E.
           assert (Hswap : fromList
                             (swap (toList
                                      (recover_bintree
                                         g
                                         (BT_node x (BT_node xl ll lr) BT_nil)))
                                   (initial' * 2 - 1) (initial' - 1))
                           = recover_bintree
                               g
                               (BT_node xl (BT_node x ll lr) BT_nil)).
           { admit "". }
           rewrite Hswap.
           unfold initial'.
           rewrite E in Hsubcom. destruct n as [|n];[inversion Hsubcom;inversion H_l|].
           replace (S (encodeIdx (btctx2idx g)) * 2) with
             (S (encodeIdx (btctx2idx (btctx_left xl BT_nil g)))).
           2 :{ simpl. rewrite encode_last. nia. }
             replace (toList (recover_bintree g (BT_node xl (BT_node x ll lr) BT_nil)))
               with (toList (recover_bintree
                               (btctx_left xl BT_nil g)
                               (BT_node x ll lr))) by auto.
             inversion Hsubcom.
             { deflag. eapply (IHn n); ss; et.
               - intros. ss. apply (equicomplete_thm g t). rewrite E.
                 econs;auto;try apply bteq_refl;auto. econs;apply bteq_refl. assumption.
               - inversion H_l.
                 eapply complete_node_perfect_complete;eauto.
                 apply perfect'2complete';auto.
               - rewrite encode_last. rewrite <- toList_length. rewrite E in Htreele2.
                 split;try nia. admit "".
               - intros. ss. rewrite permutation. rewrite E. admit "".
               - instantiate (1 := xl). solve_heap Hheap_ch.
               - intros t' HH j Hj.
                 apply Hheap_nch;auto.
                 destruct Hheap_ch as [H' [H'' X]]. inversion H'. inversion H''. inversion HH.
                 + econs;simpl;auto;try nia. all : cycle 1.
                   eapply heap_erase_priority;eauto. apply heap_nil.
                 + econs;simpl;auto;try nia;econs;simpl;auto;try nia.
             }
             { deflag. eapply (IHn n); ss; et.
               - intros. ss. apply (equicomplete_thm g t). rewrite E.
                econs;auto;try apply bteq_refl;auto. econs;apply bteq_refl. assumption.
               - inversion H_l.
                 + eapply complete_node_perfect_complete;eauto.
                 + eapply complete_node_complete_perfect;eauto.
               - rewrite encode_last. rewrite <- toList_length. rewrite E in Htreele2.
                 split;try nia. admit "".
               - intros. ss. rewrite permutation. rewrite E. admit "".
               - instantiate (1 := xl). solve_heap Hheap_ch.
               - intros t' HH j Hj.
                 apply Hheap_nch;auto.
                 destruct Hheap_ch as [H' [H'' X]]. inversion H'. inversion H''. inversion HH.
                 + econs;simpl;auto;try nia. all : cycle 1.
                   eapply heap_erase_priority;eauto. apply heap_nil.
                 + econs;simpl;auto;try nia;econs;simpl;auto;try nia.
             }
  Qed.

  Lemma sim_heapify (sk : alist string Sk.gdef) :
    sim_fnsem wf top2
              ("heapify",
               fun_to_tgt "Heapsort" (GlobalStb sk) {| fsb_fspec := heapify_spec; fsb_body := fun _ => triggerNB |})
              ("heapify", cfunU Heapsort1.heapify_body).
  (* Proof with lia || eauto.
    (** "Lemmas" *)
    pose proof (bteq_shape_refl := @bteq_refl Z).
    pose proof (bteq_shape_sym := @bteq_sym Z).
    pose proof (bteq_shape_node := @bteq_node Z).
    pose proof (plus1minus1 := fun n : nat => Nat.add_sub n 1).
    pose proof (recover_upd_root_repr := fun (t : bintree Z) t_ne_nil k g => recover_upd_root_repr_upd t k g t_ne_nil).
    assert (shape_eq_perfect' : forall (t : bintree Z) t', bteq_shape t t' -> forall rk : nat, perfect' t rk -> perfect' t' rk).
    { intros t t' t_shape_eq_t'.
      induction t_shape_eq_t' as [ | x l r x' l' r' l_shape_eq_l' IH_l r_shape_eq_r' IH_r]; intros rk t_shape_eq_t'...
      inversion t_shape_eq_t'; subst; clear t_shape_eq_t'; [econs 2]...
    }
    assert (shape_eq_complete' : forall (t : bintree Z) t', bteq_shape t t' -> forall rk : nat, complete' t rk -> complete' t' rk).
    { intros t t' t_shape_eq_t'.
      induction t_shape_eq_t' as [ | x l r x' l' r' l_shape_eq_l' IH_l r_shape_eq_r' IH_r]; intros rk t_shape_eq_t'...
      inversion t_shape_eq_t'; subst; clear t_shape_eq_t'; [econs 2 | econs 3]...
    }
    assert (shape_eq_complete : forall (t : bintree Z) t', bteq_shape t t' -> (complete t <-> complete t')).
    { intros t t' t_shape_eq_t'. split; intros [rk H_complete']; exists rk... }
    assert (btctx2idx_encode_eq : forall (g : btctx Z) ds,
      ds = btctx2idx g ->
      (HeapsortHeader.encode ds + 1 =? 1)%nat =
      match g with
      | btctx_top => true
      | _ => false
      end
    ).
    { destruct g as [ | x r g | x l g]; intros ds ?; subst ds; (apply Nat.eqb_eq || apply Nat.eqb_neq)... all: simpl; rewrite encode_last... }
    assert (upd_equiv_upd_root : forall (t : bintree Z) k, t <> BT_nil -> upd (toList t) 0 k = toList (upd_root k t)).
    { intros t k t_ne_nil. rewrite upd_spec. destruct t as [ | x l r]; [contradiction | cbn; f_equal]. }
    assert (upd_perm_cons_tail : forall (t : bintree Z) k, t <> BT_nil -> upd (toList t) 0 k ≡ₚ k :: list.tail (toList t)).
    { intros t k t_ne_nil. rewrite upd_spec. destruct t as [ | x l r]; [contradiction | now cbn; rewrite drop_0]. }
    assert (upd_root_eq_shape : forall (t : bintree Z) k, t <> BT_nil -> bteq_shape t (upd_root k t)).
    { intros [ | x l r] k t_ne_nil; [contradiction | econs 2; apply bteq_refl]. }
    assert (recover_upd_root_eq_shape : forall (t : bintree Z) t', bteq_shape t t' -> forall g, bteq_shape (recover_bintree g t) (recover_bintree g t') ).
    { intros t t' H_shape_eq g. revert t t' H_shape_eq. induction g as [ | x r g IH | x l g IH]; simpl; intros t t' H_shape_eq... all: apply IH; econs 2... all: apply bteq_refl. }
    Opaque div swap Nat.leb Nat.ltb Z.ltb toList.
    (** "Entering the function" *)
    init. harg. destruct x as [[tree p] k]. mDesAll; subst. clear PURE1. des; subst. steps. astop. steps.
    (** "Invariants" *)
    set (par := fun g' =>
      match g' with
      | btctx_top => p
      | btctx_left p' _ _ => p'
      | btctx_right p' _ _ => p'
      end
    ).
    replace (strings.length (toList tree)) with (btsize tree) by now rewrite toList_length.
    remember (toList tree, 1) as xs_and_i eqn: H_init. destruct xs_and_i as [xs i].
    remember (tree) as t eqn: t_init in H_init.
    assert (xs_init : xs = toList t) by congruence. assert (i_init : i = 1) by congruence. clear H_init.
    replace (1) with (HeapsortHeader.encode [] + 1) in i_init by reflexivity.
    remember (@nil dir_t) as ds eqn: ds_init in i_init; subst i.
    assert (t_nonempty : t <> BT_nil).
    { rewrite t_init. destruct tree; [inv PURE2 | discriminate]. }
    assert (xs_nonempty : xs <> []).
    { destruct t; [contradiction | now rewrite xs_init]. }
    assert (H_recover : xs = toList (recover_bintree btctx_top t)).
    { rewrite xs_init; rewrite t_init... }
    remember (@btctx_top Z) as g eqn: g_init in H_recover.
    assert (t_complete : complete t).
    { now rewrite t_init. }
    assert (H_complete : complete (recover_bintree g t)).
    { now rewrite g_init. }
    assert (H_permutation : toList (recover_bintree g (upd_root k t)) ≡ₚ k :: list.tail (toList tree)).
    { rewrite g_init; cbn. now transitivity (upd (toList t) 0 k); [rewrite upd_equiv_upd_root | rewrite <- t_init; apply upd_perm_cons_tail]. }
    clear xs_nonempty.
    assert (t_subtree : option_subtree ds tree = Some t).
    { now rewrite t_init; rewrite ds_init. }
    assert (H_btctx_idx : ds = btctx2idx g).
    { now rewrite g_init; rewrite ds_init. }
    assert (g_heap_pr : forall t', bteq_shape t t' -> heap_pr Z.ge (par g) t' -> heap_pr Z.ge p (recover_bintree g t')).
    { rewrite g_init... }
    assert (t_heap_pr : heap_pr Z.ge (par g) t).
    { rewrite g_init; rewrite t_init. simpl. clear t_init. induction PURE4 as [ | x l r R_x_l R_x_r H_heap_l IH_heap_l H_heap_r IH_heap_r]; econs... apply Some_inj in PURE2. rewrite PURE2... }
    assert (H_xs_length : strings.length xs = btsize tree).
    { rewrite xs_init. rewrite t_init. apply toList_length. }
    (** "Entering the first loop" *)
    clear t_init xs_init ds_init g_init.
    deflag; revert xs g ds t_nonempty H_recover H_permutation H_complete t_subtree H_btctx_idx t_complete t_heap_pr g_heap_pr H_xs_length.
    induction t as [ | x l IH_l r IH_r]; i; [now contradiction t_nonempty | rewrite unfold_iter_eq; steps_weak].
    set (obs_if1 := (HeapsortHeader.encode ds + 1) * 2 <=? btsize tree).
    set (obs_if2 := (HeapsortHeader.encode ds + 1) * 2 <? btsize tree).
    assert (H_option_root_l : HeapsortHeader.lookup xs ((HeapsortHeader.encode ds + 1) * 2 - 1) = option_root l).
    { replace ((HeapsortHeader.encode ds + 1) * 2 - 1) with (2 * HeapsortHeader.encode ds + 1) by lia.
      replace ((2 * HeapsortHeader.encode ds + 1)) with (HeapsortHeader.encode (ds ++ [Dir_left])) by apply encode_last.
      replace (ds ++ [Dir_left]) with (btctx2idx (btctx_left x r g)) by now rewrite H_btctx_idx.
      rewrite H_recover. exact (btctx_lookup (btctx_left x r g) l).
    }
    assert (H_option_root_r : HeapsortHeader.lookup xs ((HeapsortHeader.encode ds + 1) * 2) = option_root r).
    { replace ((HeapsortHeader.encode ds + 1) * 2) with (2 * HeapsortHeader.encode ds + 2) by lia.
      replace (2 * HeapsortHeader.encode ds + 2) with (HeapsortHeader.encode (ds ++ [Dir_right])) by apply encode_last.
      replace (ds ++ [Dir_right]) with (btctx2idx (btctx_right x l g)) by now rewrite H_btctx_idx.
      rewrite H_recover. exact (btctx_lookup (btctx_right x l g) r).
    }
    rewrite H_option_root_l; rewrite H_option_root_r.
    revert H_option_root_l H_option_root_r.
    replace ((HeapsortHeader.encode ds + 1) * 2) with (2 * (HeapsortHeader.encode ds + 1)) by lia.
    replace (HeapsortHeader.lookup xs (2 * (HeapsortHeader.encode ds + 1) - 1)) with (HeapsortHeader.lookup xs (2 * HeapsortHeader.encode ds + 1)) by now f_equal; lia.
    replace (HeapsortHeader.lookup xs (2 * (HeapsortHeader.encode ds + 1))) with (HeapsortHeader.lookup xs (2 * HeapsortHeader.encode ds + 2)) by now f_equal; lia.
    replace (2 * (HeapsortHeader.encode ds + 1) + 1) with ((2 * HeapsortHeader.encode ds + 2) + 1) by lia.
    replace (2 * (HeapsortHeader.encode ds + 1)) with ((2 * HeapsortHeader.encode ds + 1) + 1) by lia.
    replace (2 * HeapsortHeader.encode ds + 1) with (HeapsortHeader.encode (ds ++ [Dir_left])) by exact (HeapsortHeader.encode_last ds Dir_left).
    replace (2 * HeapsortHeader.encode ds + 2) with (HeapsortHeader.encode (ds ++ [Dir_right])) by exact (HeapsortHeader.encode_last ds Dir_right).
    intros H_option_root_l H_option_root_r.
    destruct obs_if1 eqn: H_obs_if1; [apply Nat.leb_le in H_obs_if1 | apply Nat.leb_nle in H_obs_if1]; steps_weak.
    { (** "Iterating the first loop" *)
      destruct (option_root l) as [x_l | ]; [steps_weak | apply nth_error_None in H_option_root_l].
      2: replace (HeapsortHeader.encode (ds ++ [Dir_left])) with (2 * HeapsortHeader.encode ds + 1) in H_option_root_l by now rewrite encode_last...
      destruct obs_if2 eqn: H_obs_if2; [apply Nat.ltb_lt in H_obs_if2 | apply Nat.ltb_nlt in H_obs_if2]; steps_weak.
      destruct (option_root r) as [x_r | ]; [steps_weak | apply nth_error_None in H_option_root_r].
      2: replace (HeapsortHeader.encode (ds ++ [Dir_right])) with (2 * HeapsortHeader.encode ds + 2) in H_option_root_r by now rewrite encode_last...
      destruct ((x_l <? x_r)%Z) eqn: H_obs_if3; [apply Z.ltb_lt in H_obs_if3 | apply Z.ltb_nlt in H_obs_if3]; steps_weak.
      all: repeat rewrite plus1minus1.
      - rewrite H_option_root_r; steps_weak.
        deflag; eapply IH_r with (g := btctx_right x_r l g).
        all: admit "".
      - rewrite H_option_root_l; steps_weak.
        deflag; eapply IH_l with (g := btctx_left x_l r g).
        all: admit "".
      - deflag; eapply IH_l with (g := btctx_left x_l r g).
        all: admit "".
    }
    (** "Leaving the first loop" *)
    clear IH_l IH_r.
    assert (option_root_l_None : option_root l = None).
    { rewrite <- H_option_root_l. apply nth_error_None. rewrite encode_last... }
    assert (option_root_r_None : option_root r = None).
    { rewrite <- H_option_root_r. apply nth_error_None. rewrite encode_last... }
    assert (l_is_nil : l = BT_nil) by now destruct l. assert (r_is_nil : r = BT_nil) by now destruct r. subst l r.
    remember (BT_node x BT_nil BT_nil) as t eqn: t_is_leaf.
    clear option_root_l_None option_root_r_None t_subtree H_option_root_l H_option_root_r.
    (** "Invariants" *)
    assert (H_heap_pr : forall p', (p' >= k)%Z -> heap_pr Z.ge p' (upd_root k t)).
    { rewrite t_is_leaf. simpl. intros p' H_k_ge_p'. econs 2; try now econs 1... }
    (** "Entering the second loop" *)
    clear x obs_if1 obs_if2 H_obs_if1 t_is_leaf t_heap_pr.
    deflag; revert xs ds t t_nonempty H_recover H_permutation H_complete H_heap_pr g_heap_pr t_complete H_btctx_idx H_xs_length.
    induction g as [ | x r g IH | x l g IH]; i; rewrite unfold_iter_eq.
    all: pose proof (btctx2idx_encode_eq _ _ H_btctx_idx) as H_obs_if1.
    - rewrite H_obs_if1; steps_weak.
      { (** "Leaving the second loop" *)
        force_l. eexists. steps_weak. hret tt; ss.
        iModIntro. iSplit... iSplit... iPureIntro.
        exists (upd_root k t). rewrite H_btctx_idx. cbn; splits.
        - f_equal. rewrite H_recover. apply upd_equiv_upd_root...
        - destruct H_complete as [t_rk H_complete']. exists t_rk.
          destruct H_complete'; [econs 1 | econs 2 | econs 3]...
        - now transitivity (toList (upd_root k t)).
        - apply g_heap_pr...
      }
    - rewrite H_obs_if1; steps_weak.
      pose proof (btctx_lookup g (BT_node x t r)) as H_par. simpl in H_recover. rewrite <- H_recover in H_par. unfold option_root in H_par.
      assert (H_par_i : (HeapsortHeader.encode ds + 1) `div` 2 = HeapsortHeader.encode (btctx2idx g) + 1).
      { rewrite H_btctx_idx. simpl. rewrite encode_last.
        pose proof (Nat.div_add 0 (HeapsortHeader.encode (btctx2idx g) + 1) 2).
        replace ((2 * HeapsortHeader.encode (btctx2idx g) + 1 + 1) `div` 2) with ((0 + (HeapsortHeader.encode (btctx2idx g) + 1) * 2) `div` 2)...
        f_equal; lia.
      }
      rewrite H_par_i. repeat rewrite plus1minus1. rewrite H_par. steps_weak.
      destruct ((k <? x)%Z) eqn: H_obs_if2; [apply Z.ltb_lt in H_obs_if2 | apply Z.ltb_nlt in H_obs_if2]; steps_weak.
      { (** "Leaving the second loop" *)
        force_l. eexists. steps_weak. hret tt; ss.
        iModIntro. iSplit... iSplit... iPureIntro.
        exists (recover_bintree g (BT_node x (upd_root k t) r)); splits.
        - f_equal. symmetry. rewrite H_btctx_idx. rewrite H_recover.
          exact (recover_upd_root_repr t t_nonempty k (btctx_left x r g)).
        - eapply shape_eq_complete; [apply recover_upd_root_eq_shape | exact H_complete]...
        - now transitivity (toList (recover_bintree g (BT_node x (upd_root k t) r))).
        - apply g_heap_pr... apply H_heap_pr...
      }
      assert (t_nonempty_next : BT_node x (upd_root x t) r <> BT_nil) by discriminate.
      assert (H_recover_next : upd xs (HeapsortHeader.encode ds) x = toList (recover_bintree g (BT_node x (upd_root x t) r))).
      { replace (toList (recover_bintree g (BT_node x (upd_root x t) r))) with (upd (toList (recover_bintree g (BT_node x t r))) (HeapsortHeader.encode (btctx2idx g ++ [Dir_left])) x).
        - rewrite H_recover. rewrite H_btctx_idx...
        - symmetry. exact (recover_upd_root_repr t t_nonempty x (btctx_left x r g)).
      }
      assert (H_complete_next : complete (recover_bintree g (BT_node x (upd_root x t) r))).
      { apply shape_eq_complete with (t := (recover_bintree (btctx_left x r g) t))... simpl... }
      deflag; eapply IH with (t := BT_node x (upd_root x t) r)...
      
      deflag; eapply IH with (t := BT_node x (upd_root x t) r)...
      +       
      + pose proof recover_upd_root_repr.
      all: admit "".
    - rewrite H_obs_if1; steps_weak.
      pose proof (btctx_lookup g (BT_node x l t)) as H_par. simpl in H_recover. rewrite <- H_recover in H_par. unfold option_root in H_par.
      assert (H_par_i : (HeapsortHeader.encode ds + 1) `div` 2 = HeapsortHeader.encode (btctx2idx g) + 1).
      { rewrite H_btctx_idx. simpl. rewrite encode_last.
        pose proof (Nat.div_add 1 (HeapsortHeader.encode (btctx2idx g) + 1) 2).
        replace ((2 * HeapsortHeader.encode (btctx2idx g) + 2 + 1) `div` 2) with ((1 + (HeapsortHeader.encode (btctx2idx g) + 1) * 2) `div` 2)...
        f_equal; lia.
      }
      rewrite H_par_i. repeat rewrite plus1minus1. rewrite H_par. steps_weak.
      destruct ((k <? x)%Z) eqn: H_obs_if2; [apply Z.ltb_lt in H_obs_if2 | apply Z.ltb_nlt in H_obs_if2]; steps_weak.
      { (** "Leaving the second loop" *)
        force_l. eexists. steps_weak. hret tt; ss.
        iModIntro. iSplit... iSplit... iPureIntro.
        exists (recover_bintree g (BT_node x l (upd_root k t))); splits.
        - f_equal. symmetry. rewrite H_btctx_idx. rewrite H_recover.
          exact (recover_upd_root_repr t t_nonempty k (btctx_right x l g)).
        - eapply shape_eq_complete; [apply recover_upd_root_eq_shape | exact H_complete]...
        - now transitivity (toList (recover_bintree g (BT_node x l (upd_root k t)))).
        - apply g_heap_pr... apply H_heap_pr...
      }
      deflag; eapply IH with (t := BT_node x l (upd_root x t)).
      all: admit "".
    (** "Leaving the function" *)
    Unshelve.
    Transparent div Nat.leb Nat.ltb Z.ltb toList.
  Qed. *)
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
    repl xs with (toList tree) at 2 3
      by (subst; eapply toList_fromList).
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
