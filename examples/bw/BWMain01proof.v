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
    { unfold mainbody, mainF, ccall, hcall. init.
      (* harg_tac begin *)
      eapply (@harg_clo _ "H" "INV"); ss. clear SIMMRS mrs_src mrs_tgt. i.
      (* harg_tac end*)
      mDesAll. des; clarify.
      steps. rewrite Any.upcast_downcast in *. clarify.
      destruct (alist_find "getbool" (ClientStb ++ MainStb)) eqn:T; stb_tac; clarify.
      steps. rewrite Any.upcast_downcast. steps.



      steps.

      stb_tac.
      unfold alist_find. ss.

      astart 0. astop.
      mAssertPure (x = Z.odd a); subst.
      { iApply (bw_ra_merge with "INV H"). }
      steps. force_l. eexists.


      harg_tac. des. subst. rewrite Any.upcast_downcast. ss.
      iRefresh. iDestruct PRE. iPure A. clarify. steps.
      destruct (alist_find "getbool" (ClientStb ++ MainStb)) eqn:T; stb_tac; clarify.
      steps. rewrite Any.upcast_downcast. ss. steps.
      hcall_tac tt ord_top (@URA.unit Σ) PRE (@URA.unit Σ); ss.
      { esplits; eauto. }
      des; clarify. steps. rewrite Any.upcast_downcast in *. ss. clarify. steps.
      unfold TODO.unbool. des_ifs; ss.
      { steps. astart 10.
  Admitted.

End SIMMODSEM.
