Require Import HoareDef MWHeader MWCImp MWC9 SimModSem.
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

Require Import HTactics.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB.
Require Import MWCImp9proofDef.

Set Implicit Arguments.

Local Open Scope nat_scope.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk,
      stb_incl (to_stb_context ["Map.new"; "Map.access"; "Map.update"; "App.init"; "App.run"; "MW.loop"]
                               (MemStb)) (global_stb sk).
  Import ImpNotations.

  Ltac isteps := repeat (steps; imp_steps).

  Lemma _main_sim sk (SKINCL: Sk.incl (defs MWprog) sk) (SKWF: Sk.wf sk):
    sim_fnsem (wf (Sk.load_skenv sk)) le
              ("main", KModSem.disclose_ksb_tgt "MW" (global_stb sk) (ksb_trivial (cfunU mainF)))
              ("main", cfunU (eval_imp (Sk.load_skenv sk) MWCImp.mainF)).
  Proof.
    eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF.
    hexploit (SKINCL "gv0"); ss; eauto 10. intros [blk0 FIND0].
    hexploit (SKINCL "gv1"); ss; eauto 10. intros [blk1 FIND1].
    { kinit. harg. mDesAll; des; clarify. unfold mainF, MWCImp.mainF, ccallU.
      set (Sk.load_skenv sk) as ske in *.
      fold (wf ske).
      isteps. rewrite unfold_eval_imp. isteps.
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { rewrite Any.pair_split. steps. }
      rewrite Any.upcast_split. steps.
      des_ifs; cycle 1.
      { contradict n. solve_NoDup. }
      steps. erewrite STBINCL; cycle 1. { stb_tac; ss. } isteps.
      hcall None None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. iPureIntro. esplits; ss; et. }
      { esplits; ss; et. }
      fold (wf ske). mDesAll; des; clarify. steps. isteps. rewrite FIND0. steps.
      isteps. ss. des_ifs. mDesOr "INV"; mDesAll; des; clarify; ss.
      unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *.
      astart 1. astep "store" (tt↑). { eapply STBINCL. stb_tac; ss. } hcall (Some (_, _, _)) _ with "A1".
      { iModIntro. iSplitR; iSplits; ss; et. }
      { esplits; ss; et. }
      fold (wf ske). unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps. astop. steps.

      apply Any.pair_inj in H2. des; clarify.
      unfold unblk in *. des_ifs.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. unfold var_points_to. rewrite FIND0. rewrite FIND1. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      astart 1. astep "store" (tt↑). { eapply STBINCL. stb_tac; ss. } rewrite FIND1. isteps.
      hcall (Some (_, _, _)) _ with "A".
      { iModIntro. iSplitR; iSplits; ss; et. }
      { esplits; ss; et. }
      fold (wf ske). unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps. astop. steps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. unfold var_points_to in *. rewrite FIND0. rewrite FIND1. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. unfold var_points_to in *. rewrite FIND0. rewrite FIND1. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). unfold var_points_to in *. rewrite FIND0 in *. rewrite FIND1 in *. ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      hret None; ss.
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. unfold var_points_to in *. rewrite FIND0. rewrite FIND1. iFrame. ss. }
    }
  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
