Require Import HoareDef MutHeader MutF0 MutF1 SimModSem.
Require Import Coqlib.
Require Import Universe.
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

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).

  Let wf: W -> Prop :=
    mk_wf (fun (_: unit) _ _ => (True: iProp)%I) top4.

  Theorem correct: ModPair.sim MutF1.F MutF0.F.
  Proof.
    econs; ss.
    2: { i. inv WF. econs; ss. }
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf); et.
    2: { econs; ss; red; uipropall. }
    econs; ss. init. harg. mDesAll.
    des; clarify. unfold fF, ccall.
    apply Any.upcast_inj in PURE0. des; clarify.
    rewrite Any.upcast_downcast. steps. astart 10.
    force_r.
    { eapply mut_max_intrange. auto. } steps.
    destruct (dec (Z.of_nat x) 0%Z).
    - destruct x; ss. astop. force_l. eexists. steps.
      hret _; ss. et.
    - destruct x; [ss|]. rewrite Nat2Z.inj_succ. steps. acatch.
      hcall _ _ _ with "*"; auto.
      { iPureIntro.
        replace (Z.succ (Z.of_nat x) - 1)%Z with (Z.of_nat x) by lia.
        esplits; et. lia. }
      { splits; ss; eauto with ord_step. }
      i. mDesAll. des; clarify. eapply Any.upcast_inj in PURE1. des; clarify.
      rewrite Any.upcast_downcast. steps. astop.
      force_l. eexists. steps. force_r.
      { eapply mut_max_sum_intrange. lia. } steps.
      force_r.
      { replace (Z.succ x + sum x)%Z with ((sum (S x)): Z).
        { eapply mut_max_sum_intrange. lia. }
        { ss. lia. }
      } steps.
      hret _; ss. iPureIntro. esplits; ss.
      f_equal. f_equal. lia.
      Unshelve. all: ss.
  Qed.

End SIMMODSEM.
