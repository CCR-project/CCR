Require Import HoareDef IntroHeader IntroGSep0 IntroGSep1 SimModSem.
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
      (fun _ _ st_tgt => (∃ (usable: bool), OwnM(IRA.module(usable): IRA.t) ∧ ⌜st_tgt = usable↑⌝)%I)
  .

  Theorem correct: refines2 [IntroGSep0.G] [IntroGSep1.G].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { ss. }
    { esplits. econs; ss. eapply to_semantic. iIntros "H". iSplits; ss. }

    econs; ss. init. harg. mDesAll.
    des; clarify. unfold gF, ccallU. steps. astart 10.
    des_ifs.
    - steps. acatch. hcall _ _ with "*"; auto.
      { iModIntro. iFrame. iSplits; try by (iPureIntro; refl).
        2: { iPureIntro. do 3 f_equal. instantiate (1:=x - 1). lia. }
        { ss. }
        { iPureIntro. lia. }
      }
      { esplits; ss; et. eapply OrdArith.lt_from_nat. lia. }
      steps. astop. ss. steps. mDesAll; clarify. rewrite Any.upcast_downcast. ss. steps.
      mAssert _ with "A INV1".
      { iCombine "A" "INV1" as "A". iApply (OwnM_Upd with "A").
        instantiate (1:=@URA.add IRA.t (IRA.client false) (IRA.module false)). r. ur. i. des_ifs. }
      force_l. eexists. steps. hret _; ss.
      { iMod "A1". iModIntro. iDestruct "A1" as "[B C]". iFrame. iSplits; ss; et. iPureIntro. do 2 f_equal. lia. }
    - steps.
      mAssertPure False.
      { iCombine "A" "INV" as "A". iOwnWf "A". ur in H0. des_ifs. }
      ss.
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
