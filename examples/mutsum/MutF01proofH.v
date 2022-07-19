Require Import HoareDef MutHeader MutF0 MutF1 SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import HTactics ProofMode HSim IProofMode.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.
  Context `{Σ: GRA.t}.

  Theorem correct: refines2 [MutF0.F] [MutF1.F].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=mk_wf world_wf_trivial) (le:=world_le_trivial); et.
    2: { eapply world_wf_trivial_init. }
    econs; ss. econs; ss.
    apply isim_fun_to_tgt; auto. i; ss.
    iIntros "[INV %]". des. clarify.
    iApply isim_trivial_init_pure. iFrame.
    unfold fF. ss. hred. iApply isim_trivial_bind.
    iApply isim_trivial_assume. iSplit.
    { iPureIntro. eapply mut_max_intrange. auto. }
    destruct (dec (Z.of_nat x) 0%Z).
    - destruct x; ss. hred. iApply isim_trivial_ret.
      iSplit; auto. iApply world_wf_trivial_inv_with.
    - destruct x; [ss|]. rewrite Nat2Z.inj_succ. hred.
      iApply isim_trivial_bind. iApply isim_trivial_ccallU.
      { eapply fn_has_spec_in_stb; eauto.
        instantiate (1:=x). ss. eauto with ord_step.
      }
      ss. iSplits; eauto.
      { replace (Z.succ (Z.of_nat x) - 1)%Z with (Z.of_nat x) by lia. auto. }
      { iPureIntro. lia. }
      iIntros (? ?) "[% %]". subst.
      iExists _. iSplit; [eauto|]. hred.
      iApply isim_trivial_ret. iSplits; eauto.
      { iApply world_wf_trivial_inv_with. }
      iPureIntro. f_equal. f_equal. lia.
  Qed.
End SIMMODSEM.
