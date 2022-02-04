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
  Admitted.

  Lemma sim_heapify (sk : alist string Sk.gdef) :
    sim_fnsem wf top2
              ("heapify",
               fun_to_tgt "Heapsort" (GlobalStb sk) {| fsb_fspec := heapify_spec; fsb_body := cfunN heapify_body |})
              ("heapify", cfunU Heapsort1.heapify_body).
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
    
    astart (length xs / 2 + length xs).
    
    remember (length xs / 2) as l. clear Heql.
    
    set (xs' := xs). unfold xs' at 1.
    assert (xs' ≡ₚ xs) by eapply Permutation_refl.
    remember xs' as xs0. clear xs' Heqxs0.
    revert xs0 H w ctx mp_src mp_tgt mr_src WF ACC.
    induction l.
    - i. rewrite unfold_iter_eq. steps.
      admit "heapify loop".
    - i. rewrite unfold_iter_eq. steps.
      acatch.
      { instantiate (1 := create_spec). admit "stb". }
      { instantiate (1 := l + length xs0).
        eapply OrdArith.lt_from_nat.
        lia.
      }
      hcall _ _ with "".
      { iModIntro. iSplit; ss.
        admit "we have to construct tree".
      }
    (*
    2: { i.
    rewrite unfold_iter_eq.
    steps. des_if. steps.
    2: {
      steps.
      acatch.
      instantiate (1:=create_spec).
      admit "1".
      hcall (x,0) _ with "".
      { iModIntro. iSplit. ss. iSplit.
        2: { iPureIntro. eauto. }
        admit "1".
      }
      ss. splits; ss. oauto.
      steps.
      Search ITree.iter.
     *)
  Admitted.

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
