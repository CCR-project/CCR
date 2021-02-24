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

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



(* TODO: move to SimModSem & add cpn3_wcompat *)
Hint Resolve sim_itree_mon: paco.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Local Opaque GRA.to_URA sum.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = Maps.add "F" (ε, tt↑) Maps.empty>>) /\
      (<<TGT: mrps_tgt0 = Maps.add "F" (ε, tt↑) Maps.empty>>)
  .

  Theorem correct: ModSemPair.sim MutF1.FSem MutF0.FSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss. init.
    unfold fF, checkWf, forge, discard, put. steps.
    des; clarify. rewrite Any.upcast_downcast in *. clarify. apply_all_once Any.upcast_inj. des. clarify. clear_tac.
    unfold APC. unfold interp_hCallE_tgt. steps. rewrite URA.unit_idl in *.
    destruct (dec (Z.of_nat x0) 0%Z).
    - destruct x0; ss. force_l. exists 0. steps.
      force_l. eexists. force_l. eexists. force_l.
      exists (ε, x1). steps. force_l.
      { refl. }
      steps. force_l. exists ε. force_l. esplits; eauto.
      steps. force_l. exists x1. rewrite URA.unit_idl.
      force_l; auto. steps.

    - destruct x0; [ss|]. rewrite Nat2Z.inj_succ.
      force_l. exists 1. steps.
      force_l. exists false. steps. force_l. eexists ("g", [Vint (Z.of_nat x0)]↑).
      steps. rewrite Any.upcast_downcast. ss.
      unfold HoareCall, checkWf, forge, discard, put. steps.
      force_l. eexists (_, _). steps. force_l.
      { refl. }
      steps. force_l. eexists. steps. force_l. eexists. force_l.
      { rewrite URA.unit_idl. refl. }
      steps. force_l. eexists. force_l. eexists. force_l. eexists. force_l.
      { esplits; et. }
      force_l.
      { splits; ss. }
      replace (Z.succ (Z.of_nat x0) - 1)%Z with (Z.of_nat x0).
      2: { lia. }
      ired. gstep. econs; ss. i. des; clarify. unfold alist_add. ss. exists 100.
      steps. des; clarify. rewrite Any.upcast_downcast in *. clarify. apply_all_once Any.upcast_inj. des. clarify. clear_tac.
      steps. force_l. eexists. force_l. eexists. force_l. eexists (_, _).
      steps. force_l.
      { refl. }
      steps. force_l. eexists. force_l.
      { esplits; eauto. f_equal. f_equal. Local Transparent sum. ss. lia. }
      steps. force_l. eexists. force_l; eauto. steps.
  Qed.

End SIMMODSEM.
