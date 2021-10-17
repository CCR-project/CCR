Require Import HoareDef MWHeader MWA0 MW1 SimModSem.
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



Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    (* mk_wf (fun (_: unit) mp_src0 mp_tgt0 => (⌜∃ lst0, mp_src0 = lst0↑ ∧ mp_tgt0 = lst0.(lst_map)↑⌝)%I). *)
    fun (_: unit) '(mp_src0, mp_tgt0) => ∃ lst0, mp_src0 = lst0↑ ∧ mp_tgt0 = lst0.(lst_map)↑
  .

  Theorem correct: refines2 [MWA0.MW] [MW1.MW].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et.
    { ss. }
    2: { esplits; ss; et. }
    econs; ss.
    { init. unfold mainF, MWA0.mainF, ccallU. steps. des; clarify. steps. gstep; econs; et.
      { r. esplits; et. }
      ii; ss. des; clarify. esplits; et. steps. unfold unwrapU. des_ifs; ss; steps. rr. esplits; et. econs; et.
    }
    econs; ss.
    { init. unfold loopF, MWA0.loopF, ccallU. steps. unfold unwrapU. des_ifs; steps. des_ifs; steps. des; clarify. des_ifs; steps.
      gstep; econs; et.
      { econs; et. }
      steps. ii. des; clarify. esplits; et. des_ifs; steps. rr; esplits; et. rr; econs; et.
    }
    econs; ss.
    { init. unfold putF, MWA0.putF, ccallU. steps. force_l. exists false. steps. rr in WF. des; clarify.
      rewrite Any.upcast_downcast in *; clarify. steps. gstep; econs; et. { econs; et. } ii; ss. des; clarify.
      esplits; et. steps. r. esplits; et. r. econs; et. esplits; try refl. ss. TTTTTTTTTTTTTTTTTTTTTT et. ss.
      des_ifs; steps. des_ifs; steps. des; clarify. des_ifs; steps.
      gstep; econs; et.
      { econs; et. }
      steps. ii. des; clarify. esplits; et. des_ifs; steps. rr; esplits; et. rr; econs; et.
    }
    init. harg. mDesAll.
    des; clarify. unfold fF, ccallU. steps. astart 10.
    force_r.
    { eapply mut_max_intrange. auto. } steps.
    destruct (dec (Z.of_nat x) 0%Z).
    - destruct x; ss. astop. force_l. eexists. steps.
      hret _; ss.
    - destruct x; [ss|]. rewrite Nat2Z.inj_succ. steps. force_r.
      { rewrite <- Nat2Z.inj_succ. eapply mut_max_intrange_sub1. auto. }
      steps. acatch. hcall _ _ _ with "*"; auto.
      { iPureIntro.
        replace (Z.succ (Z.of_nat x) - 1)%Z with (Z.of_nat x) by lia.
        esplits; et. lia. }
      { splits; ss; eauto with ord_step. }
      i. mDesAll. des; clarify.
      steps. astop.
      force_l. eexists. steps. force_r.
      { eapply mut_max_sum_intrange. lia. } steps.
      force_r.
      { replace (Z.succ x + sum x)%Z with ((sum (S x)): Z).
        { eapply mut_max_sum_intrange. lia. }
        { ss. lia. }
      } steps.
      hret _; ss. iPureIntro. esplits; ss.
      f_equal. f_equal. lia.
      Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
