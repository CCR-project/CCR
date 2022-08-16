Require Import HoareDef SimModSem.
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
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Require Import MWMap0 MWMapImp.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.

  Import ImpNotations.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Let wf: unit -> W -> Prop :=
    fun _ '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = tt↑>>) /\
      (<<TGT: mrps_tgt0 = tt↑>>)
  .

  Theorem correct:
    refines2 [MWMapImp.Map] [MWMap0.Map].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss.
    { init.
      unfold newF, new.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n. solve_NoDup. }
      imp_steps.
      unfold ccallU. imp_steps.
      red. esplits; et.
    }
    econs; ss.
    { init.
      steps.
      unfold updateF, update, ccallU. steps. rewrite unfold_eval_imp. imp_steps.
      des_ifs.
      2:{ contradict n0. solve_NoDup. }
      steps. imp_steps. des; clarify. unfold unblk in *. des_ifs. steps.
      imp_steps. uo. unfold scale_int. des_ifs. cbn. steps.
      imp_steps. uo. unfold scale_int. des_ifs. cbn. steps.
      imp_steps. uo. unfold scale_int. des_ifs. cbn. steps.
      { r. esplits; et. }
    }
    econs; ss.
    { init.
      steps.
      unfold accessF, access, ccallU. steps. rewrite unfold_eval_imp. imp_steps.
      des_ifs.
      2:{ contradict n0. solve_NoDup. }
      steps. imp_steps. des; clarify. unfold unblk in *. des_ifs. steps.
      imp_steps. uo. unfold scale_int. des_ifs. cbn. steps.
      imp_steps. uo. unfold scale_int. des_ifs. cbn. steps.
      imp_steps. uo. unfold scale_int. des_ifs. cbn. steps.
      { r. esplits; et. }
    }
    econs; ss.
    { init.
      steps.
      unfold loopF, loop, ccallU. steps. rewrite unfold_eval_imp. imp_steps.
      des_ifs.
      2:{ contradict n0. solve_NoDup. }
      steps. imp_steps. des; clarify. unfold unblk in *. des_ifs. steps.
      imp_steps. uo. unfold scale_int. ss. des; clarify.
      destruct (dec z0 z).
      - subst. rewrite Z.eqb_refl. des_ifs_safe. cbn. steps.
        imp_steps. uo. unfold scale_int. des_ifs. cbn. steps.
        imp_steps. uo. unfold scale_int. des_ifs. cbn. steps.
        imp_steps. steps.
        { r. esplits; et. }
      - subst. cbn. steps. des_ifs. { rewrite Z.eqb_eq in Heq. ss. } steps.
        imp_steps. uo. unfold scale_int. des_ifs. cbn. steps.
        imp_steps. uo. unfold scale_int. des_ifs. cbn. steps.
        imp_steps. steps.
        { r. esplits; et. }
    }
    Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
