Require Import Main0 Main1 HoareDef SimModSem.
Require Import Coqlib.
Require Import Universe.
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
Require Import TODOYJ.
Require Import HTactics Logic IPM.
Require Import Mem1.

Set Implicit Arguments.

Local Open Scope nat_scope.





Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  (* Let wf: W -> Prop := top1. *)
  Let wf: W -> Prop := fun '(mrps_src0, mrps_tgt0) =>
                         exists mr_src0 mp_src0 mr_tgt0 mp_tgt0,
                           (<<SRC: mrps_src0 = (mr_src0, mp_src0)>>)
                           /\ (<<TGT: mrps_tgt0 = (mr_tgt0, mp_tgt0)>>)
                           (* /\ (<<SIM: iHyp ⌜True⌝ mr_src0>>) *)
  .

  Theorem sim_modsem: ModSemPair.sim Main1.MainSem Main0.MainSem.
  Proof.
    econs; ss.
    econs; ss.
    { unfold mainF. init. harg. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *. iRefresh.
      iDestruct PRE; subst. unfold mainBody. steps.
      astart 2.
      astep "alloc" ([Vint 1], true).

      hcall_tac __ (ord_pure 0) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ); ss; et.
      { iRefresh. instantiate (1:=Some _). iSplitP; ss. left; iRefresh. iExists __. iSplitP; ss.
        iSplitP; ss. iSplitP; ss. split; ss. instantiate (1:=1). ss. }
      iDestruct POST; cycle 1. { iPure POST. des; ss. }
      repeat iDestruct POST; ss. iPure POST. repeat iDestruct A. iPure A. clarify. apply Any.upcast_inj in A. des; clarify.
      steps. rewrite Any.upcast_downcast in *. clarify.
      rename x3 into blk.
      astep "store" ([Vptr blk 0; Vint 42], true).

      hcall_tac __ (ord_pure 0) (@URA.unit Σ) (@URA.unit Σ) A0; ss; et.
      { iRefresh. instantiate (1:=Some _). repeat (iSplitP; ss). left. iExists __. instantiate (1:=(_, _, _)). cbn.
        repeat iSplitP; ss. iExists __. repeat iSplitP; ss; et. }
      iDestruct POST; cycle 1. { iPure POST. des; ss. }
      repeat iDestruct POST; ss. iPure POST. repeat iDestruct A. iPure A. clarify. iRefresh.
      steps. astop. steps. force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.

      hcall_tac __ ord_top (@URA.unit Σ) A (@URA.unit Σ); ss; et.
      { rewrite OpenDef.upcast_pair_downcast. ss. }
      iPure POST. subst. clarify. steps.

      astart 1.
      astep "load" ([Vptr blk 0], true).

      hcall_tac __ (ord_pure 0) (@URA.unit Σ) (@URA.unit Σ) A; ss; et.
      { iRefresh. instantiate (1:=Some _). iSplitP; ss. left; iRefresh. iExists __. repeat iSplitP; ss.
        instantiate (1:=(_, _, _)). steps. iRefresh. repeat iSplitP; ss; et. }
      iDestruct POST; cycle 1. { iPure POST. des; ss. }
      repeat iDestruct POST; ss. iPure POST. repeat iDestruct A. iPure A. clarify. iRefresh.
      steps. astop. steps. rewrite Any.upcast_downcast in *. clarify. iDestruct A. iPure A0.
      apply Any.upcast_inj in A0. des; clarify.
      hret_tac (@URA.unit Σ) (@URA.unit Σ); ss.
    }
    Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Theorem correct: ModPair.sim Main1.Main Main0.Main.
  Proof.
    econs; ss.
    { ii. eapply adequacy_lift. eapply sim_modsem. }
    ii; ss. repeat (econs; ss).
  Qed.

End SIMMOD.
