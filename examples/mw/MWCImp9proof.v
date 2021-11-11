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
Require Import MWCImp9proofDef MWCImp9proofMain MWCImp9proofLoop MWCImp9proofPut MWCImp9proofGet.

Set Implicit Arguments.

Local Open Scope nat_scope.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk,
      stb_incl (to_stb_context ["Map.new"; "Map.access"; "Map.update"; "App.init"; "App.run"; "MW.loop"]
                               (MemStb)) (global_stb sk).

  Theorem correct:
    refines2 [MWCImp.MW] [MWC9.MW (global_stb)].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf (Sk.load_skenv sk)) (le:=le); et; ss; swap 2 3.
    { typeclasses eauto. }
    { eexists. econs. eapply to_semantic. iIntros "[A B]". iLeft. iSplits; ss; et. iFrame. iSplits; ss; et. }

    (* eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF. *)
    (* hexploit (SKINCL "gv0"); ss; eauto. intros [blk0 FIND0]. *)
    (* hexploit (SKINCL "gv1"); ss; eauto 10. intros [blk1 FIND1]. *)

    econs; ss.
    { eapply _main_sim; et. }

    econs; ss.
    { eapply _loop_sim; et. }

    econs; ss.
    { eapply _put_sim; et. }

    econs; ss.
    { eapply _get_sim; et. }

  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
