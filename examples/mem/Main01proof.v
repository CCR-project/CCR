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
Require Import HTactics Logic YPM.
Require Import Mem1.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.


Ltac hcall_tac x o MR_SRC1 FR_SRC1 RARG_SRC :=
  let mr_src1 := r_gather MR_SRC1 in
  let fr_src1 := r_gather FR_SRC1 in
  let rarg_src := r_gather RARG_SRC in
  let tac0 := try by (eapply URA.extends_updatable; r_equalize; r_solve) in
  let tac1 := (on_gwf ltac:(fun H => clear H);
               let WF := fresh "WF" in
               let tmp := fresh "_tmp_" in
               let GWF := fresh "GWF" in
               let mr_src1 := fresh "mr_src1" in
               let mp_src1 := fresh "mp_src1" in
               let mr_tgt1 := fresh "mr_tgt1" in
               let mp_tgt1 := fresh "mp_tgt1" in
               intros ? [mr_src1 mp_src1] [mr_tgt1 mp_tgt1] ? WF; cbn in WF; desH WF; subst;
               esplits; ss; et; intros tmp ?; assert(GWF: ☀) by (split; [refl|exact tmp]); clear tmp; iRefresh; iClears') in
  prep;
  (match x with
   | ltac_wild =>
     match o with
     | ltac_wild => eapply (@hcall_clo _ mr_src1 fr_src1 rarg_src)
     | _ => eapply (@hcall_clo _ mr_src1 fr_src1 rarg_src o)
     end
   | _ => eapply (@hcall_clo _ mr_src1 fr_src1 rarg_src o _ x)
   end);
  shelve_goal; [on_gwf ltac:(fun GWF => apply GWF)|tac0|eapply OrdArith.lt_from_nat; lia|..|tac1]
.

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
    { unfold mainF. init. harg_tac. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *. iRefresh.
      iDestruct PRE; subst. unfold mainBody. steps.
      astart 2.
      astep "malloc" ([Vint 1], true).

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
      { rewrite Open.upcast_pair_downcast. ss. }
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
