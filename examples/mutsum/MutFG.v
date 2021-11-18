Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import MutHeader.
Require Import MutFImp MutGImp MutF0 MutG0 MutMain0 MutF1 MutG1 MutMain1.
Require Import MutFImp0proof MutGImp0proof MutF01proof MutG01proof MutMain01proof.
Require Import ProofMode.

Set Implicit Arguments.





Section PROOF.

  Definition Σ: GRA.t := fun _ => of_RA.t RA.empty.
  Local Existing Instance Σ.

  Let smds := [MutMain1.SMain; MutF1.SF; MutG1.SG].
  Let GlobalStb := fun sk => to_stb (SMod.get_stb smds sk).

  Definition FGImp: list Mod.t := [MutMain0.Main ; MutFImp.F ; MutGImp.G].
  Definition FG0: list Mod.t := [MutMain0.Main ; MutF0.F ; MutG0.G].
  Definition FG1: list Mod.t := List.map (SMod.to_tgt GlobalStb) smds.
  Definition FG2: list Mod.t := List.map (SMod.to_src) smds.

  Lemma FGImp0_correct:
    refines2 FGImp FG0.
  Proof.
    eapply refines2_cons.
    { refl. }
    eapply refines2_cons.
    { eapply MutFImp0proof.correct. }
    { eapply MutGImp0proof.correct. }
  Qed.

  Lemma FG01_correct:
    refines2 FG0 FG1.
  Proof.
    eapply refines2_cons.
    { eapply MutMain01proof.correct. }
    eapply refines2_cons.
    { eapply MutF01proof.correct. }
    { eapply MutG01proof.correct. }
  Qed.

  Lemma FG12_correct:
    refines_closed (Mod.add_list FG1) (Mod.add_list FG2).
  Proof.
    unfold FG1, FG2.
    eapply adequacy_type.
    { instantiate (1:=ε). cbn. rewrite ! URA.unit_id. eapply URA.wf_unit. }
    { i. ss. clarify. ss. exists tt. splits; ss.
      { iIntros "H". iPureIntro. splits; auto. }
      { ii. iPureIntro. i. des; auto. }
    }
  Qed.

  Theorem FG_correct:
    refines_closed (Mod.add_list FGImp) (Mod.add_list FG2).
  Proof.
    etrans.
    { eapply refines_close. eapply FGImp0_correct. }
    etrans.
    { eapply refines_close. eapply FG01_correct. }
    { eapply FG12_correct. }
  Qed.

End PROOF.

Definition mutsum_imp := ModSemL.initial_itr (ModL.enclose (Mod.add_list FGImp)) None.
Definition mutsum := ModSemL.initial_itr (ModL.enclose (Mod.add_list FG2)) None.
