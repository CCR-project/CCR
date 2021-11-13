Require Import HoareDef STB CannonRA CannonMain0 CannonMain1 Cannon0 Cannon1.
Require Import Cannon01proof CannonMain01proof.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Hoare ProofMode.

Set Implicit Arguments.


Section PROOF.

  Let Σ: GRA.t := GRA.of_list [CannonRA].
  Local Existing Instance Σ.

  Let CannonRA_inG: @GRA.inG CannonRA Σ.
  Proof. exists 0. ss. Defined.
  Local Existing Instance CannonRA_inG.

  Section ERASE.
    Variable num_fire: nat.

    Let smd := [Cannon1.SCannon; CannonMain1.SMain num_fire].
    Let stb := fun sk => to_closed_stb (SMod.get_stb smd sk).
    Let prog_src := List.map SMod.to_src smd.
    Let prog_tgt := List.map (SMod.to_tgt stb) smd.

    Theorem cannon_erase_spec:
      refines_closed
        (Mod.add_list prog_tgt)
        (Mod.add_list prog_src).
    Proof.
      eapply adequacy_type_closed with (entry_r := GRA.embed Ball).
      { g_wf_tac. eapply BallReady_wf. }
      { unfold to_closed_stb. cbn. i. ss. clarify.
        exists tt. split; ss.
        { iIntros "H". iSplits; ss. }
        { split; ss. ii. iPureIntro. i. des. auto. }
      }
    Qed.
  End ERASE.

  Theorem cannon_1_correct:
    refines_closed
      (Mod.add_list ([Cannon0.Cannon; CannonMain0.Main 1]))
      (Mod.add_list (List.map SMod.to_src [SCannon; SMain 1])).
  Proof.
    etrans; [|eapply cannon_erase_spec].
    { eapply refines_close. eapply refines2_cons.
      { eapply Cannon01proof.correct. }
      { eapply CannonMain01proof.correct. i. ss. }
    }
  Qed.

End PROOF.
