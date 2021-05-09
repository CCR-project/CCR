Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef BW1 BWMain0 BWMain1 SimModSem.

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
Require Import HTactics.
Require Import Logic YPM.

Set Implicit Arguments.

Local Open Scope nat_scope.




Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG BW1.bwRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Let wf: W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ _ => (⌜True⌝)%I)
      top3
  .

  Theorem correct: ModSemPair.sim BWMain1.MainSem BWMain0.MainSem.
  Proof.
    econstructor 1 with (wf:=wf); et; swap 2 3.
    { ss. red. econs; et; ss. red. uipropall. }

    econs; ss.
    { unfold mainbody, mainF, ccall, hcall. init. harg.
      mDesAll. des; clarify.
      steps. rewrite Any.upcast_downcast in *. clarify.
      destruct (alist_find "getbool" (BWStb ++ ClientStb ++ MainStb)) eqn:T; stb_tac; clarify.
      steps. rewrite Any.upcast_downcast. steps.
      hcall _ _ _ with "".
      { ss. }
      { iModIntro. iSplit; ss. }
      { splits; ss. ss. }
      mDesAll. clarify. steps.
      rewrite Any.upcast_downcast in *. clarify.
      unfold TODO.unbool in *. astart 3.
      (* TODO: use bind rule to reduce redundancy *)
      des_ifs.
      { steps. acatch.
        hcall _ _ _ with "*"; auto.
        { eauto with ord_step. }
        mDesAll. clarify. steps.
        rewrite Any.upcast_downcast in *. clarify. acatch.

        hcall _ _ _ with "*"; auto.
        { eauto with ord_step. }
        mDesAll. clarify.
        rewrite Any.upcast_downcast in *. clarify.
        eapply Any.upcast_inj in PURE5. des; clarify. steps.
        astop. steps. force_l. eexists. steps.
        force_l; et. steps.
        destruct (alist_find "putint" (BWStb ++ ClientStb ++ MainStb)) eqn:T; stb_tac; clarify.
        steps. rewrite Any.upcast_downcast. steps.

        hcall ord_top _ _ with ""; auto.
        mDesAll. steps. rewrite Any.upcast_downcast in *. clarify.
        steps. hret _; ss.
        { iModIntro. iSplit; ss. iSplit; ss. iStopProof.
          (* TODO: fix top1 => TRUE: iProp *)
          red. uipropall. }
      }
      { steps. acatch.
        hcall _ _ _ with "*"; auto.
        { eauto with ord_step. }
        mDesAll. clarify. steps.
        rewrite Any.upcast_downcast in *. clarify. astop.
        eapply Any.upcast_inj in PURE4. des; clarify.
        steps. force_l. eexists. steps.
        force_l; et. steps.
        destruct (alist_find "putint" (BWStb ++ ClientStb ++ MainStb)) eqn:T; stb_tac; clarify.
        steps. rewrite Any.upcast_downcast. steps.

        hcall ord_top _ _ with ""; auto.
        mDesAll. steps. rewrite Any.upcast_downcast in *. clarify.
        steps. hret _; ss.
        { iModIntro. iSplit; ss. iSplit; ss. iStopProof.
          (* TODO: fix top1 => TRUE: iProp *)
          red. uipropall. }
      }
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
