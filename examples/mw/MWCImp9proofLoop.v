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


  Lemma _loop_sim sk (SKINCL: Sk.incl (defs MWprog) sk) (SKWF: Sk.wf sk):
    sim_fnsem (wf (Sk.load_skenv sk)) le
              ("MW.loop", KModSem.disclose_ksb_tgt "MW" (global_stb sk) (ksb_trivial (cfunU loopF)))
              ("MW.loop", cfunU (eval_imp (Sk.load_skenv sk) MWCImp.loopF)).
  Proof.
    eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF.
    hexploit (SKINCL "gv0"); ss; eauto 10. intros [blk0 FIND0].
    hexploit (SKINCL "gv1"); ss; eauto 10. intros [blk1 FIND1].
    { kinit. harg. mDesAll; des; clarify. unfold loopF, MWCImp.loopF, ccallU.
      set (Sk.load_skenv sk) as ske in *.
      fold (wf ske).
      isteps. rewrite unfold_eval_imp. isteps.
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { rewrite Any.pair_split. steps. }
      rewrite Any.upcast_split. steps.
      des_ifs; cycle 1.
      { contradict n. solve_NoDup. }
      steps. isteps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ None with "*".
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
      { esplits; ss; et. }
      fold (wf ske). ss. des_ifs.
      mDesOr "INV"; mDesAll; des; clarify; ss. isteps.

      hret None; ss.
      { iModIntro. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame. ss. }
    }
    Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
