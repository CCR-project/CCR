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

  Ltac isteps := repeat (steps; imp_steps; eauto).

  Lemma _loop_sim sk (wf: unit -> Any.t * Any.t -> Prop) (SKINCL: Sk.incl (defs MWprog) sk) (SKWF: Sk.wf sk):
    sim_fnsem wf top2
              ("MW.loop", cfunU (loopF))
              ("MW.loop", cfunU (eval_imp (Sk.load_skenv sk) MWCImp.loopF)).
  Proof.
    { init.
      unfold loopF, MWCImp.loopF, ccallU.
      steps. rewrite unfold_eval_imp. isteps.
      des_ifs.
      2:{ exfalso; apply n. solve_NoDup. }
      isteps. des; clarify.
      r. esplits; et.
    }
  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
