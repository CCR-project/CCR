Require Import Mem1.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef Stack0 Stack1 SimModSem.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import HTactics TODOYJ YPM.

Set Implicit Arguments.

Local Open Scope nat_scope.








Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).
  Eval compute in (@URA.car Mem1._memRA).

  Let wf: W -> Prop :=
    mk_wf (fun (_: unit) _ => (True: iProp)%I) top3.

  Local Opaque points_to.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.

  Theorem correct: ModSemPair.sim Stack1.StackSem Stack0.StackSem.
  Proof.
    econstructor 1 with (wf:=wf); et; swap 2 3.
    { red. econs; ss. red. uipropall. }

    econs; ss.
    (* pop *)
    { (* arg *)
      unfold popF. init. harg. destruct x.
      mDesAll. clarify. rewrite Any.upcast_downcast. steps.
      eapply Any.upcast_inj in PURE1. des; clarify. steps.
      unfold ccall. steps. astart 10.

      (* load *)
      acatch. hcall _ (n, 0%Z, a0) _ with "A1"; auto.
      { iModIntro. iFrame. iSplit; ss. }
      { splits; ss. eauto with ord_step. }
      mDesAll. clarify. eapply Any.upcast_inj in PURE1. des; clarify.
      steps. erewrite Any.upcast_downcast in *. steps.

      destruct l; ss.
      (* l = [] *)
      { mDesAll. subst.
        (* cmp *)
        steps. acatch. hcall _ _ _ with "INV"; auto.
        { instantiate (2:=(true,_)). ss. iModIntro.
          iSplitR; ss. iSplitL; ss. iSplitL; ss. iSplitR; ss.
          iRight. iRight. iRight. iRight. iPureIntro. ss. }
        { split; ss. eauto with ord_step. }
        mDesAll. clarify. eapply Any.upcast_inj in PURE3. des; clarify.
        steps. erewrite Any.upcast_downcast in *. steps.

        (* ret *)
        astop. force_l. eexists. hret _; ss.
      }

      (* l = lhd :: ltl *)
      mDesAll. subst.
      rewrite points_to_split in ACC. mDesOwn "A2".

      (* cmp *)
      steps. acatch. hcall _ _ _ with "A2"; auto.
      { instantiate (2:=(false,_)). ss. iModIntro.
        iSplitR; ss. iSplitL; ss. iSplitL; ss.
        iSplitR; ss. iLeft. iExists _, _, _. iSplit; ss. }
      { split; ss. eauto with ord_step. }
      ss. mDesAll. clarify. eapply Any.upcast_inj in PURE3. des; clarify.
      steps. erewrite Any.upcast_downcast in *. steps.

      (* load *)
      steps. acatch. hcall _ (a0, 0%Z, v0) _ with "INV1"; auto.
      { iModIntro. iSplitR; ss. iSplitL; ss. iSplitL; ss. iSplitR; ss. }
      { split; ss. eauto with ord_step. }
      ss. mDesAll. clarify. eapply Any.upcast_inj in PURE4. des; clarify.
      steps. erewrite Any.upcast_downcast in *. clarify.

      (* load *)
      steps. acatch. hcall _ (a0, (0+1)%Z, a2) _ with "A"; auto.
      { iModIntro. iSplitR; ss. iSplitL; ss. iSplitL; ss. iSplitR; ss. }
      { split; ss. eauto with ord_step. }
      ss. mDesAll. clarify. eapply Any.upcast_inj in PURE5. des; clarify.
      steps. erewrite Any.upcast_downcast in *. clarify.

      (* free *)
      steps. acatch. hcall _ (a0, 0%Z) _ with "INV2"; auto.
      { iModIntro. iSplitR; ss. iSplitL; ss. iSplitL; ss.
        iExists _. iSplitR; ss. }
      { split; ss. eauto with ord_step. }
      ss. mDesAll. clarify. des; clarify.
      steps. erewrite Any.upcast_downcast in *. clarify.

      (* free *)
      steps. acatch. hcall _ (a0, (0+1)%Z) _ with "INV1"; auto.
      { iModIntro. iSplitR; ss. iSplitL; ss. iSplitL; ss.
        iExists _. iSplitR; ss. }
      { split; ss. eauto with ord_step. }
      ss. mDesAll. clarify. des; clarify.
      steps. erewrite Any.upcast_downcast in *. clarify.

      (* store *)
      steps. acatch. hcall _ (n, 0%Z, v0) _ with "INV"; auto.
      { iModIntro. iSplitR; ss. iSplitL; ss. iSplitL; ss.
        iExists _. iSplitR; ss. }
      { split; ss. eauto with ord_step. }
      ss. mDesAll. clarify. des; clarify.
      steps. erewrite Any.upcast_downcast in *. clarify.

      (* ret *)
      astop. force_l. eexists. hret _; ss.
      iModIntro. iSplitR; ss. iSplitL; ss. iSplitR; ss.
      iExists _. iFrame.
    }

    econs; ss.
    (* pop2 *)
    { (* arg *)
      unfold pop2F. init. harg. destruct x.
      mDesAll. clarify. rewrite Any.upcast_downcast. steps.
      eapply Any.upcast_inj in PURE1. des; clarify. steps.
      unfold ccall. steps. astart 10.

      destruct l; ss.
      (* l = [] *)
      { mDesAll. subst.
        (* cmp *)
        steps. acatch. hcall _ _ _ with "A"; auto.
        { instantiate (2:=(true,_)). ss. iModIntro.
          iSplitR; ss. iSplitL; ss. iSplitL; ss. iSplitR; ss.
          iRight. iRight. iRight. iRight. iPureIntro. ss. }
        { split; ss. eauto with ord_step. }
        mDesAll. clarify. eapply Any.upcast_inj in PURE1. des; clarify.
        steps. erewrite Any.upcast_downcast in *. steps.

        (* ret *)
        astop. force_l. eexists. hret _; ss.
      }

      (* l = lhd :: ltl *)
      mDesAll. subst.
      rewrite points_to_split in ACC. mDesOwn "A3".

      (* cmp *)
      steps. acatch. hcall _ _ _ with "A3"; auto.
      { instantiate (2:=(false,_)). ss. iModIntro.
        iSplitR; ss. iSplitL; ss. iSplitL; ss.
        iSplitR; ss. iLeft. iExists _, _, _. iSplit; ss. }
      { split; ss. eauto with ord_step. }
      ss. mDesAll. clarify. eapply Any.upcast_inj in PURE1. des; clarify.
      steps. erewrite Any.upcast_downcast in *. steps.

      (* load *)
      steps. acatch. hcall _ (a2, 0%Z, v) _ with "INV"; auto.
      { iModIntro. iSplitR; ss. iSplitL; ss. iSplitL; ss. iSplitR; ss. }
      { split; ss. eauto with ord_step. }
      ss. mDesAll. clarify. eapply Any.upcast_inj in PURE3. des; clarify.
      steps. erewrite Any.upcast_downcast in *. clarify.

      (* load *)
      steps. acatch. hcall _ (a2, (0+1)%Z, a3) _ with "A1"; auto.
      { iModIntro. iSplitR; ss. iSplitL; ss. iSplitL; ss. iSplitR; ss. }
      { split; ss. eauto with ord_step. }
      ss. mDesAll. clarify. eapply Any.upcast_inj in PURE4. des; clarify.
      steps. erewrite Any.upcast_downcast in *. clarify.

      (* free *)
      steps. acatch. hcall _ (a2, 0%Z) _ with "INV1"; auto.
      { iModIntro. iSplitR; ss. iSplitL; ss. iSplitL; ss.
        iExists _. iSplitR; ss. }
      { split; ss. eauto with ord_step. }
      ss. mDesAll. clarify. des; clarify.
      steps. erewrite Any.upcast_downcast in *. clarify.

      (* free *)
      steps. acatch. hcall _ (a2, (0+1)%Z) _ with "INV"; auto.
      { iModIntro. iSplitR; ss. iSplitL; ss. iSplitL; ss.
        iExists _. iSplitR; ss. }
      { split; ss. eauto with ord_step. }
      ss. mDesAll. clarify. des; clarify.
      steps. erewrite Any.upcast_downcast in *. clarify.

      (* store *)
      steps. acatch. hcall _ (n, 0%Z, v0) _ with "A"; auto.
      { iModIntro. iSplitR; ss. iSplitL; ss. iSplitL; ss.
        iExists _. iSplitR; ss. }
      { split; ss. eauto with ord_step. }
      ss. mDesAll. clarify. des; clarify.
      steps. erewrite Any.upcast_downcast in *. clarify.

      (* ret *)
      astop. force_l. eexists. hret _; ss.
      iModIntro. iSplitR; ss. iSplitL; ss.
      iExists _. iFrame. ss.
    }

    econs; ss.
    (* push *)
    { (* arg *)
      unfold pushF. init. harg. destruct x.
      mDesAll. clarify. rewrite Any.upcast_downcast. steps.
      eapply Any.upcast_inj in PURE1. des; clarify. steps.
      unfold ccall. steps. astart 10.

      (* alloc *)
      steps. acatch. hcall _ 2 _ with ""; auto.
      { split; ss. eauto with ord_step. }
      mDesAll. clarify. eapply Any.upcast_inj in PURE1. des; clarify.
      steps. erewrite Any.upcast_downcast in *. steps.
      rewrite points_to_split in ACC. mDesOwn "A1".

      (* store *)
      steps. acatch. hcall _ (a2, 0%Z, v) _ with "A1"; auto.
      { rewrite Z.add_0_l. iModIntro. iSplitR; ss. iSplitL; ss.
        iSplitL; ss. iExists _. iFrame. et. }
      { split; ss. eauto with ord_step. }
      mDesAll. clarify. erewrite Any.upcast_downcast in *. steps.

      (* store *)
      steps. acatch. hcall _ (a2, (0+1)%Z, a0) _ with "A2"; auto.
      { iModIntro. iSplitR; ss. iSplitL; ss.
        iSplitL; ss. iExists _. iFrame. et. }
      { split; ss. eauto with ord_step. }
      mDesAll. clarify. erewrite Any.upcast_downcast in *. steps.

      (* ret *)
      mCombine "INV" "INV1".
      rewrite <- points_to_split in ACC.
      astop. force_l. eexists. hret _; ss.
      iModIntro. iSplitR; ss. iSplitL; ss.
      iExists _. iSplitL; ss. iExists _, _. iSplitR "A"; ss.
      iSplitR; ss.
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
