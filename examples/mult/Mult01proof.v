Require Import HoareDef MultHeader Mult0 Mult1 SimModSem.
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

Require Import STB ProofMode.
Require Import HTactics2 ISim2 IProofMode2.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{@GRA.inG fRA Σ}.
  Context `{@GRA.inG gRA Σ}.
  Context `{@GRA.inG hRA Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ _ st_tgt => ⌜True⌝%I)
  .

  Theorem correct: refines2 [Mult0.Mult (fun _ => to_stb GlobalStb0)] [Mult1.Mult (fun _ => to_stb GlobalStb1)].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. rp; [econs|..]; try refl; cycle 1.
      { repeat f_equal. rewrite URA.unit_id; ss. }
      eapply to_semantic. iIntros "H". iSplits; ss. }

    econs; [|ss].
    { econs; r; ss. startproof.
      i. esplits; eauto.
      iIntros. iDes. iModIntro. iFrame. iSplits; ss. steps. iIntros. iDes. subst. iFrame; ss.
    }

    econs; [|ss].
    { econs; r; ss. startproof.
      i. esplits; eauto.
      iIntros. iDes. iFrame. iSplits; ss. iDestruct (OwnM_Upd with "A0") as ">A0".
      { eapply f01_update. }
      steps. iIntros. iDes. subst. iFrame; ss. iModIntro. iSplits; et. steps.
      iSplits; ss. iIntros. iSplits; ss. iIntros; iDes. iFrame. iSplits; ss. iIntros; iDes. subst.
      iFrame. iSplits; ss. steps. iSplits; ss. iIntros. iSplits; ss. iIntros. iFrame. iSplits; ss.
      iIntros. iDes; subst. iSplits; ss. steps. iIntros; iDes. iFrame.
      iDestruct (OwnM_Upd with "A0") as ">A0".
      { eapply f23_update. }
      iFrame. iModIntro. iSplits; ss.
    }

    econs; [|ss].
    { econs; r; ss. startproof.
      i. esplits; eauto.
      iIntros. iDes. iFrame. iModIntro. iSplits; ss. steps.
      iApply isim_apc_both. iFrame. iIntros.
      steps. iIntros. iDes. subst. iFrame; ss.
    }
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
