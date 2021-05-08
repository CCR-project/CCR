Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef BWMain0 BWMain1 SimModSem.

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
      destruct (alist_find "getbool" (ClientStb ++ MainStb)) eqn:T; stb_tac; clarify.
      steps. rewrite Any.upcast_downcast. steps.
      hcall _ _ _ with "".
      { ss. }
      { iModIntro. iSplit; ss. }
      { splits; ss. ss. }
      mDesAll. clarify. steps.
      rewrite Any.upcast_downcast in *. clarify.
      unfold TODO.unbool in *. astart 3. des_ifs.
      { steps. acatch.
        (* TODO: add BWStb *)
  Admitted.

End SIMMODSEM.
