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
   fun_to_tgt "Heapsort" (GlobalStb sk) {| fsb_fspec := create_spec; fsb_body := cfunN create_body |})
   ("create", cfunU Heapsort1.create_body).
  Proof.
    unfold create_body. unfold Heapsort1.create_body.
    init. harg. destruct x as [tree l]. mDesAll. clear PURE1. destruct PURE0. steps.
    astop. induction tree.
    - steps. rewrite unfold_iter_eq.
      destruct l;nia.
    - (*
        destruct H0. destruct H0. steps. rewrite unfold_iter_eq.
      destruct (l + (l + 0) <=? S n);destruct (l + (l + 0) <=? n).
      + unfold toList. rewrite toList_step_unfold. steps.
      *)
  Admitted.

  Lemma sim_heapify (sk : alist string Sk.gdef) :
    sim_fnsem wf top2
              ("heapify",
               fun_to_tgt "Heapsort" (GlobalStb sk) {| fsb_fspec := heapify_spec; fsb_body := cfunN heapify_body |})
              ("heapify", cfunU Heapsort1.heapify_body).
  Proof with eauto.
    init. harg. destruct x as [root k]. mDesAll; subst.
    clear PURE1. destruct PURE0 as [H_eq PURE]; subst.
    steps. astop. revert mrp_src mp_tgt WF k ctx mr_src PURE ACC.
    induction root as [ | x l IH_l r IH_r]; i.
    { steps. rewrite unfold_iter_eq. des_ifs. steps.
      unfold toList. rewrite toList_step_unfold. rewrite toList_step_unfold.
      steps. rewrite unfold_iter_eq. steps.
      force_l. eexists. steps. hret tt; ss.
      iModIntro. iSplit; ss. iPureIntro.
      esplits; try reflexivity.
      instantiate (1 := (BT_node k BT_nil BT_nil)).
      - rewrite toList_step_unfold. ss.
      - admit "complete".
      - rewrite toList_step_unfold. ss.
      - econs; econs.
    }
    { admit "caseOf_BT_node". }
    (* Unshelve. et. *)
  Admitted.

  Lemma sim_heapsort (sk : alist string Sk.gdef) :
    sim_fnsem wf top2
              ("heapsort", fun_to_tgt "Heapsort" (GlobalStb sk) {| fsb_fspec := heapsort_spec; fsb_body := cfunN heapsort_body |})
              ("heapsort", cfunU Heapsort1.heapsort_body).
  Proof.
    Opaque div.
    unfold Heapsort1.heapsort_body.
    init.
    harg. rename x into xs. mDesAll. clear PURE1. steps.

    remember (length xs <=? 1).
    destruct b.
    - astop. steps. force_l.
      eexists. steps.
      hret tt; ss.
      iModIntro. iSplit; ss. iPureIntro.
      esplits; try reflexivity.
      destruct xs as [| x []].
      + econs.
      + econs; econs.
      + ss.
    - assert (Hxs : length xs > 1)
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
      clear Heqtree.

      (* set l and it's initial condition *)
      remember (length (toList tree) / 2) as l.
      assert (Hₗ : l <= length (toList tree)).
      { subst.
        eapply Nat.lt_le_incl.
        eapply Nat.div_lt.
        - replace (length (toList tree)) with (length xs)
            by (eapply Permutation_length; symmetry; ss).
          lia.
        - lia.
      }
      assert (H : forall j, j > l -> heap_at Z.ge (j - 1) tree) by admit "heap".
      clear Heql.

      (* 'l' for first loop, 'length xs' for second loop *)
      astart (l + length xs).

      deflag.
      revert tree Hₚ Hₗ H w ctx mp_src mp_tgt mr_src WF ACC.
      induction l.
      + i. rewrite unfold_iter_eq. steps.
        assert (Hₕ : heap Z.ge tree) by admit "from H".
        clear H Hₗ.

        remember (length (toList tree) - 1) as l eqn: Hₗ.
        replace (length xs) with (l + 1)
          by (erewrite Permutation_length in Hₗ by eapply Hₚ; lia).

        remember ([] : list Z) as ys.
        clear Heqys.

        deflag.
        revert tree ys Hₚ Hₕ Hₗ w ctx mp_src mp_tgt mr_src WF ACC.
        induction l.
        -- i. rewrite unfold_iter_eq. steps.
           assert (length (toList tree) <= 1) by lia.
           replace (length (toList tree) <=? 1) with true
             by (symmetry; eapply leb_correct; ss).
           steps.
           astop. force_l. eexists. steps.
           hret tt; ss.
           iModIntro. iSplit; ss. iPureIntro. esplits; ss.
           ++ admit "invariant".
           ++ admit "invariant".
        -- i. rewrite unfold_iter_eq. steps.
           assert (length (toList tree) > 1) by lia.
           replace (length (toList tree) <=? 1) with false
             by (symmetry; eapply leb_correct_conv; lia).
           steps.
           admit "wip".
      + i. rewrite unfold_iter_eq. steps.
        acatch.
        { eapply STBINCL. stb_tac. ss. }
        { instantiate (1 := l + length xs).
          eapply OrdArith.lt_from_nat.
          lia.
        }
        hcall (tree, S l) _ with "".
        { iModIntro. iSplit; ss. iPureIntro. splits; ss; try lia.
          - admit "complete".
        }
        { ss. splits; et; oauto. }
        mDesAll. rename a into tree'. des. steps.
        rewrite Nat.sub_0_r.
        deflag.
        eapply IHl.
        * symmetry in PURE3. transitivity (toList tree); ss.
        * replace (length (toList tree')) with (length (toList tree))
            by (eapply Permutation_length; ss).
          lia.
        * intros. eapply PURE4. lia.
        * red. inversion WF. econs. et.
        * assumption.
    Unshelve. et.
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
