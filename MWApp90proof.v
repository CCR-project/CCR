Require Import MWApp9 MWApp0 MWHeader HoareDef SimModSem.
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
Require Import MemOpen.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    fun (_: unit) '(mp_src, mp_tgt) => mp_src = mp_tgt ∧ Any.split mp_src = None.

  Variable frds: Sk.t -> list mname.

  Theorem correct: refines2 [KMod.transl_src frds (MWApp9.KApp)] [MWApp0.App].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    2: { esplits; ss; et. rewrite Any.upcast_split; ss. }
    econs; ss.
    { init. inv WF. des; clarify.
      unfold fun_to_src, body_to_src, cfunU, cfunN, MWApp9.initF, initF, ccallU.
      steps. rewrite my_if_same. steps. des; clarify. steps.
      des_ifs; steps.
      - force_r; ss; clarify. steps.
        { r. esplits; ss; et. }
      - des; clarify. force_r; ss; clarify. steps.
        { r. esplits; ss; et. rewrite Any.upcast_split; ss. }
    }
    econs; ss.
    { init. inv WF. des; clarify.
      unfold fun_to_src, body_to_src, cfunU, cfunN, MWApp9.runF, runF, ccallU.
      steps. rewrite my_if_same. steps. des; clarify. steps.
      des_ifs; steps.
      - force_r; ss; clarify. steps.
        { r. esplits; ss; et. }
      - des; clarify. force_r; ss; clarify. steps. force_r; ss; clarify. steps.
        force_r; ss; clarify. steps. force_r; ss; clarify. steps.
        { r. esplits; ss; et. }
    }
    { admit "TODO". }
  Unshelve.
    all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
