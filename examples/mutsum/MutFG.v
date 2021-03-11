Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import MutHeader SimModSem.
Require Import MutFImp MutGImp MutF0 MutG0 MutMain0 MutF1 MutG1 MutMain1.
Require Import MutFImp0proof MutGImp0proof MutF01proof MutG01proof MutMain01proof.

Require Import HTactics.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Definition Σ: GRA.t := fun _ => of_RA.t RA.empty.
  Local Existing Instance Σ.

  Definition FGImp: Mod.t := Mod.add_list [MutMain0.main ; MutFImp.F ; MutGImp.G].

  Definition FG0: Mod.t := Mod.add_list [MutMain0.main ; MutF0.F ; MutG0.G].

  Definition FG1: Mod.t := Mod.add_list [MutMain1.main ; MutF1.F ; MutG1.G].

  Definition FG2: Mod.t :=
    Mod.add_list [
        md_src MutMain1.main mainsbtb ; (* Main *)
        md_src MutF1.F Fsbtb ;  (* F *)
        md_src MutG1.G Gsbtb  (* G *)
      ].

  Definition FG3: Mod.t := {|
    Mod.get_modsem := fun _ => {|
        ModSem.fnsems :=
          [("main", fun _ => Ret (Vint 55)↑) ;
          ("f", fun _ => trigger (Choose _)) ;
          ("g", fun _ => trigger (Choose _))];
        ModSem.initial_mrs := [("Main", (ε, tt↑)) ; ("F", (ε, tt↑)) ; ("G", (ε, tt↑))];
      |};
    Mod.sk := Sk.unit;
  |}
  .

  Lemma FGImp0_correct:
    Beh.of_program (Mod.interp FGImp) <1= Beh.of_program (Mod.interp FG0).
  Proof.
    eapply ModPair.sim_list_adequacy. econs; [|econs; [|econs; ss]].
    - split; auto.
      + ii. ss. eapply MutFImp0proof.correct.
      + i. ss. split; ss; repeat econs; eauto.
    - split; auto.
      + ii. ss. eapply MutGImp0proof.correct.
      + i. ss. split; ss; repeat econs; eauto.
  Qed.

  Lemma FG01_correct:
    Beh.of_program (Mod.interp FG0) <1= Beh.of_program (Mod.interp FG1).
  Proof.
    eapply ModPair.sim_list_adequacy_closed. econs; [|econs; [|econs; ss]].
    - split; auto.
      + ii. ss. eapply MutMain01proof.correct.
      + i. ss. split; ss; repeat econs; eauto.
    - split; auto.
      + ii. ss. eapply MutF01proof.correct.
      + i. ss. split; ss; repeat econs; eauto.
    - split; auto.
      + ii. ss. eapply MutG01proof.correct.
      + i. ss. split; ss; repeat econs; eauto.
  Qed.

  Lemma FG12_correct:
    Beh.of_program (Mod.interp FG1) <1= Beh.of_program (Mod.interp FG2).
  Proof.
    ii.
    eapply adequacy_type with (sbtb:=mainsbtb++(Fsbtb++Gsbtb)) in PR; ss.
    cbn in *. unfold compose. ss. rewrite ! URA.unit_id. apply URA.wf_unit.
    Unshelve.
    all: try (by econs; ss).
  Qed.

  Lemma FG23_correct: Beh.of_program (Mod.interp FG2) <1= Beh.of_program (Mod.interp FG3).
  Proof.
    eapply ModPair.adequacy_local_closed. econs; auto.
    2: { i. ss. split; ss; repeat (econs; eauto; ii; ss; des; clarify). }
    ii.
    eapply ModSemPair.mk with (wf:=top1) (le:=top2); ss.
    econs; [|econs; [|econs;ss]].
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src. steps.
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src.
      steps. force_l. eexists. steps.
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src.
      steps. force_l. eexists. steps.
  Qed.

  Theorem FG_correct:
    Beh.of_program (Mod.interp FGImp) <1= Beh.of_program (Mod.interp FG3).
  Proof.
    i. eapply FG23_correct, FG12_correct, FG01_correct, FGImp0_correct, PR.
  Qed.

End PROOF.

Definition mutsum_imp := ModSem.initial_itr_no_check (Mod.enclose FGImp).
Definition mutsum := ModSem.initial_itr_no_check (Mod.enclose FG3).
