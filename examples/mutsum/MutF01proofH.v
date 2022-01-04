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

Require Import HTactics ProofMode.

Set Implicit Arguments.

Local Open Scope nat_scope.


(* TODO: HSim.v *)
Require Import Red.
Require Import IRed.

Ltac hred_l := try (prw _red_gen 1 2 1 0).
Ltac hred_r := try (prw _red_gen 1 1 1 0).

Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Let wf: unit -> Any.t -> Any.t -> iProp
    := (fun _ _ _ => (True: iProp)%I).

  Require Import HSim.

  Theorem correct: refines2 [MutF0.F] [MutF1.F].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=mk_wf wf) (le:=top2); et.
    { ss. }
    2: { unfold wf. exists tt. econs; ss; red; uipropall. }
    econs; ss. init.

    harg. gfinal. right. eapply hsim_adequacy.
    ginit. eapply back_init; [clear ACC|eapply ACC]. start_ipm_proof.

    iDestruct "PRE" as "[% %]". des; clarify.
    unfold fF, ccallU. ss. hred_r.
    iApply back_bind_right_pure. iApply back_assume_tgt. iSplit.
    { iPureIntro. eapply mut_max_intrange. auto. }

    destruct (dec (Z.of_nat x) 0%Z).
    - destruct x; ss. iApply back_apc. iExists None.
      hred_r. hred_l. iApply back_choose_src. iExists _.
      iApply back_ret. iModIntro. iSplitL "INV"; eauto.
    - destruct x; [ss|]. rewrite Nat2Z.inj_succ. hred_r.
      iApply back_bind_right_pure. iApply back_assume_tgt. iSplit.
      { iPureIntro. rewrite <- Nat2Z.inj_succ. eapply mut_max_intrange_sub1. auto. }
      hred_r. iApply back_apc. iExists (Some (10: Ord.t)).
      iApply back_call_pure; [|oauto|..].
      { (* TODO: make lemmas *)
        econs; ss.
        { instantiate (1:=x). ss. eauto with ord_step. }
        { i. iIntros "H". iModIntro. iExact "H". }
        { i. iIntros "H". iModIntro. iExact "H". }
      }
      iSplitL "INV".
      { iModIntro. ss. iSplitR "INV"; eauto. iSplits; eauto.
        { iPureIntro.
          replace (Z.succ (Z.of_nat x) - 1)%Z with (Z.of_nat x) by lia.
          esplits; et.
        }
        { iPureIntro. lia. }
      }
      ss. iIntros (st_src st_tgt ret_src ret_tgt) "[H0 %]".
      des; clarify. iModIntro. hred_r.
      iApply back_bind_right_pure. iApply back_assume_tgt. iSplit.
      { iPureIntro. eapply mut_max_sum_intrange. lia. }
      hred_r. iApply back_bind_right_pure. iApply back_assume_tgt. iSplit.
      { iPureIntro. replace (Z.succ x + sum x)%Z with ((sum (S x)): Z).
        { eapply mut_max_sum_intrange. lia. }
        { ss. lia. }
      }
      hred_r. hred_l. iApply back_choose_src. iExists _.
      iApply back_ret. iModIntro. iSplitL "H0"; eauto. iSplits; eauto.
      iPureIntro. f_equal. f_equal. lia.
  Qed.

End SIMMODSEM.
