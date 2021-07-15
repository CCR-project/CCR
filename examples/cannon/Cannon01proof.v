Require Import HoareDef STB CannonRA Cannon0 Cannon1 SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import HTactics ProofMode.

Set Implicit Arguments.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG CannonRA Σ}.

  Let W: Type := Any.t * Any.t.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ((⌜st_src = (1: Z)↑ /\ st_tgt = (1: Z)↑⌝ ** OwnM (Ready))
                               ∨ OwnM (Fired))%I)
  .

  Theorem correct: refines2 [Cannon0.Cannon] [Cannon1.Cannon GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et; ss; cycle 1.
    { exists tt. red. econs. eapply to_semantic.
      iIntros "H". iLeft. iSplitR; ss. }
    econs; ss. init. unfold Cannon0.fire_body, Cannon1.fire_body. harg.
    mDesOr "INV".
    { mDesAll. des; clarify.
      steps. hret _; ss.
      iModIntro. iSplit; ss. iRight.
      iCombine "A" "A1" as "A".
      iEval (rewrite ReadyBall) in "A". ss.
    }
    { mDesAll. mAssertPure False; ss.
      iCombine "INV" "A" as "A". iOwnWf "A".
      exfalso. eapply FiredBall. et. }
    Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
