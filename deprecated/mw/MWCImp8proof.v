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

Require Import MWCImp MWC8 MWCImp8proofMain MWCImp8proofLoop MWCImp8proofPut MWCImp8proofGet.

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

  Ltac isteps := repeat (steps; imp_steps).

  Theorem correct:
    refines2 [MWCImp.MW] [MWC8.MW].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss.
    { eapply _main_sim; et. }

    econs; ss.
    { eapply _loop_sim; et. }

    econs; ss.
    { eapply _put_sim; et. }

    econs; ss.
    { eapply _get_sim; et. }
  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
