Require Import HoareDef SimModSem.
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
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Require Import MWCImp MWC8 MWCImp8proofMain MWCImp8proofLoop MWCImp8proofPut MWCImp8proofGet.

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

  TTTTTTTTTTTTTTTTTt
  Ltac isteps := repeat (steps; imp_steps).

  Theorem correct:
    refines2 [MWCImp.MW] [MWC8.MW].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss.
    { init.
      unfold mainF, MWCImp.mainF, ccallU.
      steps. rewrite unfold_eval_imp. isteps.
      des_ifs.
      2:{ exfalso; apply n1. solve_NoDup. }
      isteps. des; clarify. rewrite _UNWRAPU0. isteps. rewrite _UNWRAPU1. isteps.
      r. esplits; et.
    }
    econs; ss.
    { init.
      unfold loopF, MWCImp.loopF, ccallU.
      steps. rewrite unfold_eval_imp. isteps.
      des_ifs.
      2:{ exfalso; apply n. solve_NoDup. }
      isteps. des; clarify.
      r. esplits; et. econs; et.
    }
    econs; ss.
    { init.
      unfold putF, MWCImp.putF, ccallU.
      steps. rewrite unfold_eval_imp. isteps.
      match goal with [|- context[ ListDec.NoDup_dec ?a ?b ]] => destruct (ListDec.NoDup_dec a b) end; cycle 1.
      { contradict n1. solve_NoDup. }
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
        isteps.
        rewrite _UNWRAPU0. isteps. rewrite _UNWRAPU3. isteps.
        Local Transparent syscalls.
        cbn. des_ifs_safe. steps. isteps.
        r. esplits; et.
      - steps. bsimpl. des.
        + destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z).
          { lia. }
          isteps.
          destruct ((ZArith_dec.Z_lt_dec z 100)%Z); cycle 1.
          { lia. }
          isteps.
          rewrite _UNWRAPU1. steps. hide_k. isteps. unhide_k. steps. hide_k. isteps.
          unhide_k. steps. hide_k. isteps. unhide_k. steps. isteps.
          r. esplits; et.
        + destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z); cycle 1.
          { lia. }
          isteps.
          destruct ((ZArith_dec.Z_lt_dec z 100)%Z).
          { lia. }
          isteps.
          rewrite _UNWRAPU1. steps. hide_k. isteps. unhide_k. steps. hide_k. isteps.
          unhide_k. steps. hide_k. isteps. unhide_k. steps. isteps.
          r. esplits; et.
    }
    econs; ss.
    { init.
      unfold getF, MWCImp.getF, ccallU.
      steps. rewrite unfold_eval_imp. isteps.
      match goal with [|- context[ ListDec.NoDup_dec ?a ?b ]] => destruct (ListDec.NoDup_dec a b) end; cycle 1.
      { contradict n1. solve_NoDup. }
      match goal with
      | |- context[alist_add ?a ?b ?c] =>
        idtac a; idtac b; idtac c;
        pose (alist_add (K:=var) (R:=eq) (RD_K:=Dec_RelDec (H:=string_Dec)) (V:=val) a b c) as le
      end.
      var (@eq var) (@Dec_RelDec var string_Dec) val
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
        isteps.
        rewrite _UNWRAPU1. isteps. rewrite _UNWRAPU3. isteps.
        Local Transparent syscalls.
        cbn. des_ifs_safe. steps. isteps.
        r. esplits; et.
      - steps. bsimpl. des.
        + destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z).
          { lia. }
          isteps.
          destruct ((ZArith_dec.Z_lt_dec z 100)%Z); cycle 1.
          { lia. }
          isteps.
          rewrite _UNWRAPU2. steps. hide_k. isteps. unhide_k. steps. hide_k. isteps.
          unhide_k. steps. hide_k. isteps. unhide_k. steps. isteps.
          r. esplits; et.
        + destruct ((ZArith_dec.Z_lt_dec (- 1) z)%Z); cycle 1.
          { lia. }
          isteps.
          destruct ((ZArith_dec.Z_lt_dec z 100)%Z).
          { lia. }
          isteps.
          rewrite _UNWRAPU2. steps. hide_k. isteps. unhide_k. steps. hide_k. isteps.
          unhide_k. steps. hide_k. isteps. unhide_k. steps. isteps.
          r. esplits; et.
    }
  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
