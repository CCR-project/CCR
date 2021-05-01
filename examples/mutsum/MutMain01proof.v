Require Import HoareDef MutHeader MutMain0 MutMain1 SimModSem.
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

Require Import YPM HTactics.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



(* TODO: move to SimModSem & add cpn3_wcompat *)
Hint Resolve sim_itree_mon: paco.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = (ε, tt↑)>>) /\
      (<<TGT: mrps_tgt0 = (ε, tt↑)>>)
  .

  Theorem correct: ModPair.sim MutMain1.Main MutMain0.Main.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf); et; ss.
    econs; ss. init.
    unfold mainF, mainBody.
    harg_tac. iRefresh. iDestruct PRE. des; clarify. steps. anytac. steps.
    hcall_tac 10 (ord_pure 10) (@URA.unit (GRA.to_URA Σ)) rarg_src (@URA.unit (GRA.to_URA Σ)); splits; ss.
    iDestruct POST. des; clarify. esplits; ss. i. des; clarify.
    steps. hret_tac (@URA.unit (GRA.to_URA Σ)) (URA.add rarg_src rret); ss.
  Qed.

End SIMMODSEM.
