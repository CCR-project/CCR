Require Import HoareDef MapHeader MapI MapM MapA SimModSem MapIMproof MapMAproof.
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

Require Import ProofMode STB Invariant.
Require Import Mem1 MemOpen.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section PROOF.
  Context `{Σ: GRA.t}.

  Context `{@GRA.inG MapRA0 Σ}.
  Context `{@GRA.inG MapRA1 Σ}.
  Context `{@GRA.inG memRA Σ}.

  Theorem correct: refines2 [MapI.Map] [MapA.Map (fun _ => to_stb (MemStb ++ MapStb))].
  Proof.
    etrans.
    { eapply MapIMproof.correct.
      { i. eapply app_incl. }
      { instantiate (1:=MapStbM). i. ss. stb_tac. auto. }
    }
    { eapply MapMAproof.correct. }
  Qed.
End PROOF.
