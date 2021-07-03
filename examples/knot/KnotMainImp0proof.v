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

Require Import KnotMain0 KnotMainImp.

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
    forall ge, ModSemPair.sim (KnotMain0.MainSem ge) (KnotMainImp.KnotMainSem ge).
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss.
    { init.
      unfold fibF, fib.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n0. solve_NoDup. }
      3:{ exfalso; apply n0. solve_NoDup. }
      - imp_steps.
        unfold unint in *. des_ifs; ss; clarify.
        2:{ admit "int64 range for z". }
        imp_steps. des_ifs.
        + imp_steps. red. esplits; et.
        + imp_steps. admit "z is 1".
      - imp_steps.
        unfold unint in *. des_ifs; ss; clarify.
        2:{ admit "int64 range for z". }
        imp_steps. des_ifs.
        + imp_steps.
        + imp_steps. des_ifs.
          { depgen z. clear. i. exfalso. rewrite Z.eqb_eq in Heq3. lia. }
          imp_steps. unfold unblk in *; ss; clarify. rewrite _UNWRAPU0.
          admit "call_ban".
    }
    econs; ss.
    { init.
      steps.
      unfold mainF, main.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n0. solve_NoDup. }
      3:{ exfalso; apply n0. solve_NoDup. }
      - imp_steps.
        rewrite _UNWRAPU0. ss.
        unfold ccallU. imp_steps.
        gstep. econs; ss. i. exists 100. imp_steps.
        unfold unblk in *; ss; clarify.
        rewrite _UNWRAPU3.
        admit "call_ban".
      - admit "args to main should be []".
    }
    Unshelve. all: ss. exact Ord.O.
  Qed.

End SIMMODSEM.