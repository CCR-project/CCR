Require Import HoareDef STB CannonRA Cannon0 Cannon1 SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import HTactics ProofMode.
Require Import HSim IProofMode.

Set Implicit Arguments.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG CannonRA Σ}.

  Let W: Type := Any.t * Any.t.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Let wf: unit -> Any.t -> Any.t -> iProp :=
    (fun (_: unit) st_src st_tgt => ((⌜st_src = (1: Z)↑ /\ st_tgt = (1: Z)↑⌝ ** OwnM (Ready))
                                     ∨ OwnM (Fired))%I)
  .

  Let top2_PreOrder: @PreOrder unit top2.
  Proof. econs; eauto. Qed.
  Local Existing Instance top2_PreOrder.

  Theorem correct: refines2 [Cannon0.Cannon] [Cannon1.Cannon GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (le:=top2) (wf:=mk_wf wf); et; ss; cycle 1.
    { exists tt. econs. eapply to_semantic.
      iIntros "H". iLeft. iSplitR; ss. }
    econs; ss. econs; ss.
    apply isim_fun_to_tgt; auto. i; ss.
    unfold Cannon0.fire_body, Cannon1.fire_body.
    iIntros "[INV PRE]".
    iDestruct "PRE" as "[[% BALL] %]". subst.
    iEval (unfold inv_with, wf) in "INV".
    iDestruct "INV" as (w1) "[[[% READY] | FIRED] _]".
    { des; subst. hred_l. hred_r.
      iApply isim_pget_tgt. hred_r.
      iApply isim_syscall. iIntros (_).
      hred_l. hred_r.
      iApply isim_pput_tgt. hred_r.
      iApply isim_ret. iSplit.
      { iApply inv_with_current. iEval (unfold wf).
        iRight. iCombine "READY" "BALL" as "FIRED".
        iEval (rewrite <- ReadyBall). iApply "FIRED".
      }
      { iPureIntro. auto. }
    }
    { iCombine "FIRED" "BALL" as "FALSE".
      iPoseProof (OwnM_valid with "FALSE") as "%".
      exfalso. eapply FiredBall; auto.
    }
  Qed.

End SIMMODSEM.
