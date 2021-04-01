Require Import HoareDef MutHeader MutMain0 MutMain1 SimModSemL.
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

Require Import HTactics.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



(* TODO: move to SimModSemL & add cpn3_wcompat *)
Hint Resolve sim_itree_mon: paco.


Section SIMMODSEML.

  Context `{Σ: GRA.t}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = Maps.add "Main" (ε, tt↑) Maps.empty>>) /\
      (<<TGT: mrps_tgt0 = Maps.add "Main" (ε, tt↑) Maps.empty>>)
  .

  Theorem correct: ModSemLPair.sim MutMain1.mainSem MutMain0.mainSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss. init.
    unfold mainF, mainBody.
    harg_tac. des; clarify. steps. anytac. steps.
    hcall_tac 10 (ord_pure 10) (@URA.unit (GRA.to_URA Σ)) rarg_src (@URA.unit (GRA.to_URA Σ)); splits; ss.
    des; clarify. esplits; ss. i. des; clarify.
    steps. hret_tac (@URA.unit (GRA.to_URA Σ)) (URA.add rarg_src rret); ss.
  Qed.

End SIMMODSEML.
