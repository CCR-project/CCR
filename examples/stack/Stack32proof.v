Require Import Stack2 Stack3A HoareDef SimModSem.
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
Require Import OpenDef STB.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section REFINE.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Let W: Type := Any.t * Any.t.

  Variable frds: Sk.t -> list string.

  Let wf: _ -> W -> Prop :=
    fun (_: unit) '(st_src, st_tgt) =>
      exists (st: gmap mblock (list val)),
        st_src = st↑ /\ st_tgt = st↑.

  Theorem correct: refines2 [KMod.transl_src frds Stack3A.KStack] [Stack2.Stack].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits; et. ss. }
    econs; ss.
    { init. unfold Stack2.new_body, new_body, body_to_src.
      red in WF. des; clarify.
      match goal with
      | |- context[my_if ?cond _ _] => destruct cond
      end.
      { steps. }
      { steps. force_l. eexists. steps. force_l; et.
        steps. red. esplits; et. red. esplits; et. }
    }
    econs; ss.
    { init. unfold Stack2.pop_body, pop_body, body_to_src.
      red in WF. des; clarify.
      match goal with
      | |- context[my_if ?cond _ _] => destruct cond
      end.
      { steps. }
      { steps. rewrite _UNWRAPU1. steps. des_ifs.
        { steps. red. esplits; et. red. esplits; et. }
        { steps. red. esplits; et. red. esplits; et. }
      }
    }
    econs; ss.
    { init. unfold Stack2.push_body, push_body, body_to_src.
      red in WF. des; clarify.
      match goal with
      | |- context[my_if ?cond _ _] => destruct cond
      end.
      { steps. }
      { steps. rewrite _UNWRAPU0. steps.
        red. esplits; et. red. esplits; et. }
    }
    Unshelve. all: try exact 0. all: ss.
  Qed.
End REFINE.
