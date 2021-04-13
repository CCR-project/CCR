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

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.




Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG BW1.bwRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ) (n: Z),
        (<<SRC: mrps_src0 = (mr, tt↑)>>) /\
        (<<TGT: mrps_tgt0 = (ε, n↑)>>)
  .

  Opaque URA.unit.

  Theorem correct: ModSemPair.sim BWMain1.MainSem BWMain0.MainSem.
  Proof.
    econstructor 1 with (wf:=wf); et; swap 2 3.
    { ss. unfold alist_add; cbn. esplits; ss; eauto. }

    Opaque URA.add.
    econs; ss.
    { unfold main_body, mainF, ccall, hcall. init.
      harg_tac. des. subst. rewrite Any.upcast_downcast. ss.
      iRefresh. iDestruct PRE. iPure A. clarify. steps.
      destruct (find (fun '(_fn, _) => dec "getbool" _fn) (ClientStb ++ MainStb)) eqn:T; stb_tac; clarify.
      steps. rewrite Any.upcast_downcast. ss. steps.
      hcall_tac tt ord_top (@URA.unit Σ) PRE (@URA.unit Σ); ss.
      { esplits; eauto. }
      des; clarify. steps. rewrite Any.upcast_downcast in *. ss. clarify. steps.
      unfold TODO.unbool. des_ifs; ss.
      { steps. astart 10.
  Admitted.

End SIMMODSEM.
