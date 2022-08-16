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
    fun (_: unit) '(mp_src0, mp_tgt0) => ∃ lst0, mp_src0 = lst0↑ ∧ mp_tgt0 = lst0.(lst_map)↑ ∧ forall k, lst0.(lst_opt) k = None
  .

  Theorem correct: refines2 [MWA0.MW] [MW1.MW].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et.
    { ss. }
    2: { esplits; ss; et. }
    econs; ss.
    { init. unfold mainF, MWA0.mainF, ccallU. steps. ss. des; clarify. steps.
      { esplits; et. }
      ii; ss. des; clarify. unfold unwrapU. des_ifs; ss; steps. rr. esplits; et. econs; et.
    }
    econs; ss.
    { init. unfold loopF, MWA0.loopF, ccallU. steps. unfold unwrapU. des_ifs; steps. des_ifs; steps. ss. des; clarify. des_ifs; steps.
      { econs; et. }
      steps. ii. des; clarify. esplits; et. des_ifs; steps. rr; esplits; et.
    }
    econs; ss.
    { init. unfold putF, MWA0.putF, ccallU. steps. force_l. exists false. steps. rr in WF. des; clarify.
      rewrite Any.upcast_downcast in *; clarify. steps. { econs; et. } ii; ss. des; clarify.
      esplits; et. steps. r. esplits; ss; et.
    }
    econs; ss.
    { init. unfold getF, MWA0.getF, ccallU. steps. r in WF. des ;clarify. rewrite Any.upcast_downcast in *. steps.
      assert(NONE := WF1 z). rewrite WF1 in *. ss. des; ss. steps. 
      { ss. esplits; et. }
      ii; ss. des; clarify. esplits; et. steps. unfold unwrapU. des_ifs; steps. r. esplits; ss; et.
    }
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
