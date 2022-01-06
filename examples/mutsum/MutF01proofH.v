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

  Let W: Type := Any.t * Any.t.

  Let wf: unit -> Any.t -> Any.t -> iProp
    := (fun _ _ _ => (True: iProp)%I).

  Let top2_PreOrder: @PreOrder unit top2.
  Proof. econs; eauto. Qed.
  Local Existing Instance top2_PreOrder.

  Theorem correct: refines2 [MutF0.F] [MutF1.F].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=mk_wf wf) (le:=top2); et.
    2: { unfold wf. exists tt. econs; ss; red; uipropall. }
    econs; ss. econs; ss.
    apply back_fun_to_tgt; auto. i; ss.
    iIntros "[INV %]". des. clarify.
    unfold fF, ccallU. ss. hred_r.
    iApply back_apc. iExists (Some (10: Ord.t)).
    iApply back_assume_tgt. iSplit.
    { iPureIntro. eapply mut_max_intrange. auto. }
    destruct (dec (Z.of_nat x) 0%Z).
    - destruct x; ss. hred_r. iApply back_choose_src_trigger. iExists _.
      iApply back_ret. iSplitL "INV"; eauto.
    - destruct x; [ss|]. rewrite Nat2Z.inj_succ. hred_r.
      iApply back_call_pure.
      { eapply fn_has_spec_in_stb; eauto.
        instantiate (1:=x). ss. eauto with ord_step.
      }
      { oauto. }
      iSplitL "INV".
      { ss. iSplitR "INV"; eauto. iSplits; eauto.
        { iPureIntro.
          replace (Z.succ (Z.of_nat x) - 1)%Z with (Z.of_nat x) by lia.
          esplits; et.
        }
        { iPureIntro. lia. }
      }
      ss. iIntros (st_src0 st_tgt0 ret_src ret_tgt) "[H0 %]".
      des; clarify. hred_r.
      iApply back_choose_src_trigger. iExists _.
      iApply back_ret. iSplitL "H0"; eauto. iSplits; eauto.
      iPureIntro. f_equal. f_equal. lia.
  Qed.
End SIMMODSEM.
