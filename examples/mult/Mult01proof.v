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
Require Import HTactics2 HSim2 ISim2 IProofMode2.

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
      (fun _ _ st_tgt => OwnM fblack)
  .

  Theorem correct: refines2 [Mult0.Mult (fun _ => to_stb GlobalStb0)] [Mult1.Mult (fun _ => to_stb GlobalStb1)].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. rp; [econs|..]; try refl; cycle 1.
      { repeat f_equal. rewrite URA.unit_idl; ss. }
      eapply to_semantic. iIntros "H". iSplits; ss. }

    econs; [|ss].
    { econs; r; ss. startproof.
      (*** given src aux var, choose tgt aux var ***)
      intro n. exists n. esplits; eauto.
      (*** we have "SI * P_src" ***)
      iIntros. iDes. subst.
      (*** prove "P_tgt" ***)
      iModIntro. iFrame. iSplits; ss.
      (*** and proceed the proof. ***)
      steps.
      (*** at the end, prove "Q_tgt -* (Q_src * SI)" ***)
      iIntros. iDes. iFrame; ss.
    }

    econs; [|ss].
    { econs; r; ss. startproof.
      i. esplits; eauto.
      iIntros. iDes. subst. iFrame.
      (*** It is important that the goal contains update modality in the goal "#=> (P_tgt ∗ ...)".
           This allows update on (SI * P_src) together, not just P_src. ***)
      unfold inv_with. iDes.
      iDestruct (OwnM_Upd with "[A A0]") as ">A0".
      { eapply f01_update. }
      { iCombine "A A0" as "A". iFrame. }
      iDestruct "A0" as "[A A0]".
      iFrame. iModIntro. iSplits; et.

      (*** when calling a function, given tgt aux var, choose src aux var. ***)
      steps. iSplits; ss. iIntros. iSplits; ss.
      (*** we get "Q_tgt" ***)
      iIntros; iDes.
      (*** and prove "SI * Q_src * ..." ***)
      iFrame. iSplits; ss. iIntros; iDes. subst. iFrame. iSplits; ss.

      (*** now calling a function which has different conditions on src/tgt. the rules are the same. ***)
      steps. iSplits; ss. iIntros. iSplits; ss. iIntros. iFrame. iSplits; ss.
      iIntros. iDes; subst.

      (*** returning, same as above. ***)
      iSplits; ss. steps. iIntros; iDes.
      unfold inv_with. iDes.
      iDestruct (OwnM_Upd with "[A0 A1]") as ">A1".
      { eapply f23_update. }
      { iCombine "A0 A1" as "A0". iFrame. }
      iDestruct "A1" as "[A1 A0]".
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
