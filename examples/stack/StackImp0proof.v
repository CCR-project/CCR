Require Import HoareDef SimModSemdouble.
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
Require Import HTacticsdouble ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs2.

Require Import Stack0 StackImp.

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
    refines2 [StackImp.Stack] [Stack0.Stack].
  Proof.
    eapply adequacy_local2. econs; ss. i.
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
      unfold unblk in *. des. des_ifs_safe.
      unfold is_true. destruct (n1 =? 0)%Z eqn:N1; ss; clarify.
      - apply Z.eqb_eq in N1. clarify. ss.
        destruct (val_dec (Vint 0) (Vint 0)); ss.
        grind. ss.
        destruct v; ss.
        { steps. }
        destruct ofs; ss.
        2:{ steps. }
        imp_steps.
        uo. des_ifs_safe; ss; clarify. unfold scale_int in Heq2.
        des_ifs_safe. steps. imp_steps.
        unfold scale_int. uo; ss. des_ifs. ss.
        rewrite Z_div_same; ss. rewrite Z.add_0_l. imp_steps.
        red. esplits; et.
      - apply Z.eqb_neq in N1.
        destruct (val_dec (Vint 0) (Vint 0)); ss.
        imp_steps.
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
      unfold ccallU. imp_steps.
      rewrite _UNWRAPU1. imp_steps.
      uo; des_ifs; ss; clarify.
      2:{ unfold scale_int in *. des_ifs. }
      imp_steps.
      red. esplits; et.
    }
    Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
