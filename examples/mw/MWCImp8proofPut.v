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
  Ltac alist_tac := repeat (rewrite alist_add_find_neq; [|by ss]); rewrite alist_add_find_eq.

  Lemma _put_sim sk (wf: unit -> Any.t * Any.t -> Prop) (SKINCL: Sk.incl (defs MWprog) sk) (SKWF: Sk.wf sk):
    sim_fnsem wf top2
              ("MW.put", cfunU (putF (Sk.load_skenv sk)))
              ("MW.put", cfunU (eval_imp (Sk.load_skenv sk) MWCImp.putF)).
  Proof.
    { init.
      unfold putF, MWCImp.putF, ccallU.
      steps. rewrite unfold_eval_imp. isteps.
      match goal with [|- context[ ListDec.NoDup_dec ?a ?b ]] => destruct (ListDec.NoDup_dec a b) end; cycle 1.
      { contradict n1. solve_NoDup. }
      Global Opaque alist_add.
      isteps.
      replace (intrange_64 (- 1)) with true by ss.
      ss. clarify. steps.
      destruct ((0 <=? z)%Z && (z <? 100)%Z) eqn:T.
      - steps.
        destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z); cycle 1.
        { lia. }
        isteps.
        destruct ((ZArith_dec.Z_lt_dec z 100)%Z); cycle 1.
        { lia. }
        isteps. alist_tac. isteps. ss; clarify. steps. isteps.
        alist_tac. isteps.
        rewrite _UNWRAPU0. isteps.
        Local Transparent syscalls.
        alist_tac. isteps.
        alist_tac. isteps.
        alist_tac. isteps.
        rewrite _UNWRAPU3. isteps.
        alist_tac. isteps.
        alist_tac. isteps.
        repeat (rewrite alist_add_find_neq; [|by ss]). erewrite alist_find_some_iff; cycle 1.
        { solve_NoDup. }
        { ss. eauto 10. }
        steps. isteps.
        r. esplits; et.
      - steps. bsimpl. des.
        + destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z).
          { lia. }
          isteps.
          destruct ((ZArith_dec.Z_lt_dec z 100)%Z); cycle 1.
          { lia. }
          isteps.
          alist_tac. isteps.
          ss. clarify. isteps.
          alist_tac. isteps.
          rewrite _UNWRAPU1. steps. hide_k. isteps.
          alist_tac. isteps.
          unhide_k. steps. hide_k. isteps.
          alist_tac. isteps.
          unhide_k. steps. hide_k. isteps.
          alist_tac. isteps.
          unhide_k. steps. isteps. hide_k.
          alist_tac. isteps.
          unhide_k. steps. isteps.
          alist_tac. isteps.
          repeat (rewrite alist_add_find_neq; [|by ss]). erewrite alist_find_some_iff; cycle 1.
          { solve_NoDup. }
          { ss. eauto 10. }
          steps. isteps.
          r. esplits; et.
        + destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z); cycle 1.
          { lia. }
          isteps.
          destruct ((ZArith_dec.Z_lt_dec z 100)%Z).
          { lia. }
          isteps.
          alist_tac. isteps.
          ss. clarify. isteps.
          alist_tac. isteps.
          rewrite _UNWRAPU1. steps. hide_k. isteps.
          alist_tac. isteps.
          unhide_k. steps. hide_k. isteps.
          alist_tac. isteps.
          unhide_k. steps. hide_k. isteps.
          alist_tac. isteps.
          unhide_k. steps. isteps. hide_k.
          alist_tac. isteps.
          unhide_k. steps. isteps.
          alist_tac. isteps.
          repeat (rewrite alist_add_find_neq; [|by ss]). erewrite alist_find_some_iff; cycle 1.
          { solve_NoDup. }
          { ss. eauto 10. }
          steps. isteps.
          r. esplits; et.
    }
  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
