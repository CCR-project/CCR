Require Import HoareDef MWCImp MWC8 SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

Require Import HTactics.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.

  Ltac isteps := repeat (steps; imp_steps).

  Lemma _main_sim sk (wf: unit -> Any.t * Any.t -> Prop) (SKINCL: Sk.incl (defs MWprog) sk) (SKWF: Sk.wf sk):
    sim_fnsem wf top2
              ("main", cfunU (mainF (Sk.load_skenv sk)))
              ("main", cfunU (eval_imp (Sk.load_skenv sk) MWCImp.mainF)).
  Proof.
    { init.
      unfold mainF, MWCImp.mainF, ccallU.
      steps. rewrite unfold_eval_imp. isteps.
      des_ifs.
      2:{ exfalso; apply n1. solve_NoDup. }
      isteps. des; clarify. rewrite _UNWRAPU0. isteps. rewrite _UNWRAPU1. isteps.
      r. esplits; et.
    }
  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
