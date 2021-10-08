Require Import HoareDef IntroHeader IntroF1 IntroFSep2 SimModSem.
Import Sep.
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

Require Import HTactics ProofMode.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG IRA.t Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ _ _ => ⌜True⌝%I)
  .

  Theorem correct: refines2 [IntroF1.F] [IntroFSep2.F].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { ss. }
    { esplits. econs; ss. eapply to_semantic. iIntros "H". iSplits; ss. }

    econs; ss. init. harg. mDesAll.
    des; clarify. unfold fF, ccallU. steps. astart 10. force_r. exists x. steps. force_r; ss. steps.
    unfold Ncall. steps. des_ifs.
    - unfold ccallU. steps. acatch. hcall _ _ _ with "*"; auto.
      { esplits; ss; et. eapply OrdArith.lt_from_nat. lia. }
      steps. astop. ss. steps. mDesAll; clarify. rewrite Any.upcast_downcast. ss. steps.
      force_r; ss. steps. force_l. esplits. steps. hret _; ss.
      { iModIntro. iFrame. iSplits; ss; et. }
    - steps. astop. steps. force_l. esplits. steps.
      mAssert _ with "A".
      { iApply (OwnM_Upd with "A"). instantiate (1:=IRA.client false). r. clear_until H.
        ur. i. des_ifs.
      }
      hret _; ss.
      { iMod "A1". iModIntro. iFrame. iSplits; ss; et. }
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
