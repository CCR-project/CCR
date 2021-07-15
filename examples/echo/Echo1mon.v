Require Import Echo1 Stack3A HoareDef SimModSem.
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

  Let wf: _ -> W -> Prop := fun (_: unit) _ => True.

  Variable frds0 frds1: Sk.t -> list string.
  Hypothesis FRDS: forall sk, List.incl (frds1 sk) (frds0 sk).

  Theorem correct:
    refines2 [KMod.transl_src frds0 Echo1.KEcho] [KMod.transl_src frds1 Echo1.KEcho].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits; et. ss. }
    econs; ss.
    { init. rewrite ! my_if_same. unfold echo_body, body_to_src.
      steps. unfold unwrapU. steps. des_ifs; steps. des_ifs; steps.
      unfold ccallN. steps. unfold unwrapN. des_ifs; steps.
      des_ifs; steps. red. esplits; et. }
    econs; ss.
    { init. unfold sumbool_to_bool, body_to_src. des_ifs.
      { unfold cfunN, input_body. steps.
        unfold unwrapN, ccallU, ccallN, unwrapU, unwrapN.
        des_ifs; steps. des_ifs; steps. force_r. esplits; et.
        steps. des_ifs; steps. des_ifs; steps.
        { red. esplits; et. }
        steps. des_ifs; steps.
        red. esplits; et.
      }
      { exfalso. eapply n. ss. des; auto. right.
        eapply in_map_iff in i. des; subst. eapply in_map. eapply FRDS. et. }
      { steps. }
      { steps. }
    }
    econs; ss.
    { init. unfold sumbool_to_bool, body_to_src. des_ifs.
      { unfold cfunN, output_body. steps.
        unfold unwrapN, ccallU, ccallN, unwrapU, unwrapN.
        des_ifs; steps. des_ifs; steps.
        { red. esplits; et. }
        steps. des_ifs; steps.
        des_ifs; steps. red. esplits; et.
      }
      { exfalso. eapply n. ss. des; auto. right.
        eapply in_map_iff in i. des; subst. eapply in_map. eapply FRDS. et. }
      { steps. }
      { steps. }
    }
    Unshelve. all: ss. all: exact 0.
  Qed.
End REFINE.
