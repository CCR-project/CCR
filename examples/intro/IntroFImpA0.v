Require Import HoareDef IntroHeader IntroFImpA IntroF0 SimModSem.
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

Require Import HTactics.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.
Import ImpNotations.

Set Implicit Arguments.

Local Open Scope nat_scope.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Let wf: unit -> W -> Prop :=
    fun _ '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = tt↑>>) /\
      (<<TGT: mrps_tgt0 = tt↑>>)
  .

  Theorem correct:
    refines2 [IntroFImpA.F] [IntroF0.F].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss. init. unfold cfunU.
    unfold fF.
    unfold IntroFImpA.fF.
    (* Local Opaque vadd. *)
    steps.
    rewrite unfold_eval_imp. cbn. steps.
    (* eapply Any.downcast_upcast in _UNWRAPN. des. *)
    unfold unint, ccallU in *. destruct v; clarify; ss.
    des_ifs; try (by exfalso; apply n; solve_NoDup).
    - repeat (steps; (des_ifs; try lia; []); imp_steps). r; esplits; et.
    - repeat (steps; (des_ifs; try lia; []); imp_steps). r; esplits; et.
    - repeat (steps; (des_ifs; try lia; []); imp_steps).
      unfold Ncall.
      steps. des_ifs.
      + repeat (steps; (des_ifs; try lia; []); imp_steps).
        force_l. exists false. steps. force_l. esplits. steps.
        force_l; ss. repeat (steps; (des_ifs; try lia; []); imp_steps).
        rewrite Z.eqb_eq in *. clarify.
        r; esplits; et.
      + repeat (steps; (des_ifs; try lia; []); imp_steps).
        force_l. exists true.
        unfold ccallU.
        repeat (steps; (des_ifs; try lia; []); imp_steps).
        force_l; ss.
        repeat (steps; (des_ifs; try lia; []); imp_steps).
        r; esplits; et. do 2 f_equal. lia.
  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
