Require Import HoareDef STB CannonRA CannonMain0 CannonMain1 Cannon1 SimModSem.
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
  Hypothesis GlobalStb_fire: forall sk, GlobalStb sk "fire" = Some fire_spec.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ _ _ => (True)%I)
  .

  Theorem correct: refines2 [CannonMain0.Main 1] [CannonMain1.Main 1 GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et; ss; cycle 1.
    { exists tt. red. econs. eapply to_semantic. iIntros "H". ss. }
    econs; ss. init. harg.
    mDesAll. des; clarify. steps.
    unfold ccallU. steps. rewrite GlobalStb_fire. steps.
    hcall _ _ with "A".
    { iModIntro. iSplits; ss. }
    { splits; ss. }
    mDesAll. des; clarify. steps. hret _; ss.
    Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
