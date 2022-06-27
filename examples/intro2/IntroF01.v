Require Import HoareDef IntroHeader IntroF0 IntroF1 SimModSem.
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
    refines2 [IntroF0.F] [IntroF1.F].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss. init. unfold cfunU.
    unfold fF, IntroF0.fF.
    steps. des. clarify. ss. steps.
    force_r. { eapply max_intrange; ss. } steps.
    destruct (Z.of_nat x <? 0)%Z eqn:T; try lia.
    unfold Ncall.
    destruct (Z.of_nat x =? 0)%Z eqn:U.
    { steps. assert(x = 0) by lia. steps. force_l. exists false. steps. force_l. eexists (Vint 0). steps.
      force_l; ss. steps. force_l. eexists (Vint _). steps. force_l; ss. steps. r. esplits; et.
    }
    steps. destruct x0.
    - force_l. exists true. unfold ccallU. steps.
      rewrite Z.eqb_neq in *. force_l; ss. { splits; try lia. eapply OrdArith.lt_from_nat. lia. } steps.
      force_r. { f_equal. lia. } steps.
      force_l. eexists. steps. force_l; ss. steps. r. esplits; et. do 2 f_equal. lia.
    - steps. force_l. exists false. steps. force_l. eexists. steps. force_l; ss. steps.
      force_l. esplits. steps. force_l; ss. steps. r. esplits; et. do 2 f_equal. lia.
  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
