Require Import HoareDef SimModSem.
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
Require Import OpenDef.
Require Import Mem1 MemOpen STB.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Require Import NewStack0 NewStackImp.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.

  Import ImpNotations.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Let wf: unit -> W -> Prop :=
    fun _ '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = tt↑>>) /\
      (<<TGT: mrps_tgt0 = tt↑>>)
  .

  Theorem correct:
    forall ge, ModSemPair.sim NewStack0.StackSem (NewStackImp.StackSem ge).
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss.
    { init.
      unfold newF, new.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n. solve_NoDup. }
      imp_steps.
      unfold ccallU. imp_steps.
      gstep. econs; ss. i. exists 100. imp_steps.
      gstep. econs; ss. i. exists 100. imp_steps.
      red. esplits; et.
    }
    econs; ss.
    { init.
      steps.
      unfold popF, pop.
      unfold dec.
      Local Opaque val_dec.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n0. solve_NoDup. }
      imp_steps.
      unfold unblk in *. des_ifs.
      imp_steps.
      unfold ccallU. imp_steps.
      unfold unblk in *. des_ifs. clarify; ss.
      gstep. econs; ss. i. exists 100. imp_steps.
      gstep. econs; ss. i. exists 100. imp_steps.
      des. des_ifs_safe. ss.
      destruct (n1 =? 0)%Z eqn:N1; ss; clarify.
      - apply Z.eqb_eq in N1. clarify. ss.
        grind. ss.
        destruct v; ss.
        { steps. }
        destruct ofs; ss.
        2:{ steps. }
        imp_steps.
        gstep. econs; ss. i. exists 100. imp_steps.
        uo. des_ifs_safe; ss; clarify. unfold scale_int in Heq2.
        des_ifs_safe. steps.
        gstep. econs; ss. i. exists 100. imp_steps.
        gstep. econs; ss. i. exists 100. imp_steps.
        unfold scale_int. uo; ss. des_ifs. ss.
        rewrite Z_div_same; ss. rewrite Z.add_0_l. steps.
        gstep. econs; ss. i. exists 100. imp_steps.
        gstep. econs; ss. i. exists 100. imp_steps.
        red. esplits; et.
      - apply Z.eqb_neq in N1.
        unfold sumbool_to_bool. des_ifs.
        imp_steps.
        Local Transparent val_dec.
        red. esplits; et. unfold wf. ss.
    }
    econs; ss.
    { init.
      steps.
      unfold pushF, push.
      steps.
      rewrite unfold_eval_imp. imp_steps.
      des_ifs.
      2:{ exfalso. apply n0; solve_NoDup. }
      imp_steps.
      unfold unblk in *. des_ifs.
      imp_steps.
      unfold ccallU. steps.
      gstep. econs; ss. i. exists 100. imp_steps.
      rewrite _UNWRAPU1. imp_steps.
      gstep. econs; ss. i. exists 100. imp_steps.
      gstep. econs; ss. i. exists 100. imp_steps.
      uo; des_ifs; ss; clarify.
      2:{ unfold scale_int in *. des_ifs. }
      imp_steps.
      gstep. econs; ss. i. exists 100. imp_steps.
      gstep. econs; ss. i. exists 100. imp_steps.
      red. esplits; et.
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
