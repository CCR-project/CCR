Require Import Mem1 Mem2 HoareDef SimModSem.
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
Require Import TODOYJ.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mem0: URA.car (t:=Mem1._memRA)),
        (<<SRC: mrps_src0 = Maps.add "Mem" ((GRA.embed ((URA.black mem0))), tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "Mem" ((GRA.embed ((URA.black mem0))), tt↑) Maps.empty>>)
  .

  Local Opaque points_to.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.

  Theorem correct: ModSemPair.sim Mem2.MemSem Mem1.MemSem.
  Proof.
    admit "TODO".
  Qed.

End SIMMODSEM.
