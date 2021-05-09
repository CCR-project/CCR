Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef Client0 Client1 SimModSem.

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

Set Implicit Arguments.

Local Open Scope nat_scope.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
        (<<SRC: mrps_src0 = (ε, tt↑)>>) /\
        (<<TGT: mrps_tgt0 = (ε, tt↑)>>)
  .

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.


  Theorem correct: ModSemPair.sim Client1.ClientSem Client0.ClientSem.
  Proof.
    econstructor 1 with (wf:=wf); et; swap 2 3.
    { ss. }
    econs; ss.
    { admit "ez". }
    { admit "ez". }
  Qed.

End SIMMODSEM.
