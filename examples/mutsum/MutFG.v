Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import MutHeader SimModSemL.
Require Import MutFImp MutGImp MutF0 MutG0 MutMain0 MutF1 MutG1 MutMain1.
Require Import MutFImp0proof MutGImp0proof MutF01proof MutG01proof MutMain01proof.

Require Import HTactics.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Definition Σ: GRA.t := fun _ => of_RA.t RA.empty.
  Local Existing Instance Σ.

  Definition FGImp: ModL.t := Mod.add_list [MutMain0.main ; MutFImp.F ; MutGImp.G].

  Definition FG0: ModL.t := Mod.add_list [MutMain0.main ; MutF0.F ; MutG0.G].

  Definition FG1: ModL.t := Mod.add_list [MutMain1.main ; MutF1.F ; MutG1.G].

  Definition add_list (ms: list ModL.t): ModL.t := fold_right ModL.add ModL.empty ms.

  Definition FG2: ModL.t :=
    add_list [
        md_src MutMain1.main mainsbtb ; (* Main *)
        md_src MutF1.F Fsbtb ;  (* F *)
        md_src MutG1.G Gsbtb  (* G *)
      ].

  Definition F3: Mod.t := {|
    Mod.get_modsem := fun _ => {|
      ModSem.fnsems := [("f", fun _ => trigger (Choose _))];
      ModSem.mn := "F";
      ModSem.initial_mr := ε;
      ModSem.initial_st := tt↑;
    |};
    Mod.sk := Sk.unit;
  |}
  .

  Definition G3: Mod.t := {|
    Mod.get_modsem := fun _ => {|
      ModSem.fnsems := [("g", fun _ => trigger (Choose _))];
      ModSem.mn := "G";
      ModSem.initial_mr := ε;
      ModSem.initial_st := tt↑;
    |};
    Mod.sk := Sk.unit;
  |}
  .

  Definition Main3: Mod.t := {|
    Mod.get_modsem := fun _ => {|
      ModSem.fnsems := [("main", fun _ => trigger (Choose _))];
      ModSem.mn := "Main";
      ModSem.initial_mr := ε;
      ModSem.initial_st := tt↑;
    |};
    Mod.sk := Sk.unit;
  |}
  .

  Definition FG3: ModL.t := {|
    ModL.get_modsem := fun _ => {|
        ModSemL.fnsems :=
          [("main", fun _ => Ret (Vint 55)↑) ;
          ("f", fun _ => trigger (Choose _)) ;
          ("g", fun _ => trigger (Choose _))];
        ModSemL.initial_mrs := [("Main", (ε, tt↑)) ; ("F", (ε, tt↑)) ; ("G", (ε, tt↑))];
      |};
    ModL.sk := Sk.unit;
  |}
  .

  Lemma FGImp0_correct:
    SimModSem.refines FGImp FG0.
  Proof.
    eapply SimModSem.adequacy_local_list. econs; [|econs; [|econs; ss]].
    - econs; ss.
      i. eapply SimModSem.adequacy_lift. eapply SimModSem.ModSemPair.self_sim_mod. ss. repeat (econs; ss).
    - split; auto.
      + ii. ss. eapply SimModSem.adequacy_lift. eapply MutFImp0proof.correct.
      + i. ss. split; ss; repeat econs; eauto.
    - split; auto.
      + ii. ss. eapply SimModSem.adequacy_lift. eapply MutGImp0proof.correct.
      + i. ss. split; ss; repeat econs; eauto.
  Qed.

  Lemma FG01_correct:
    SimModSem.refines FG0 FG1.
  Proof.
    eapply SimModSem.adequacy_local_list. econs; [|econs; [|econs; ss]].
    - split; auto.
      + ii. ss. eapply SimModSem.adequacy_lift. eapply MutMain01proof.correct.
      + i. ss. split; ss; repeat econs; eauto.
    - split; auto.
      + ii. ss. eapply SimModSem.adequacy_lift. eapply MutF01proof.correct.
      + i. ss. split; ss; repeat econs; eauto.
    - split; auto.
      + ii. ss. eapply SimModSem.adequacy_lift. eapply MutG01proof.correct.
      + i. ss. split; ss; repeat econs; eauto.
  Qed.

  Lemma FG12_correct:
    Beh.of_program (ModL.compile FG1) <1= Beh.of_program (ModL.compile FG2).
  Proof.
    ii.
    TTTTTTTTTTTTTTTTTTTTTTTTTTTttt
    eapply adequacy_type with (sbtb:=mainsbtb++(Fsbtb++Gsbtb)) in PR; ss.
    instantiate (1:=ε).
    cbn in *. unfold compose. ss. rewrite ! URA.unit_id. apply URA.wf_unit.
    Unshelve.
    all: try (by econs; ss).
  Qed.

  Lemma FG23_correct: SimModSem.refines FG2 FG3.
  Proof.
    eapply SimModSem.adequacy_local.
    Opaque FG2 FG3.
    hexploit (@SimModSem.adequacy_local _ FG2 FG3); et.
    apply SimModSem.adequacy_local.
    eapply ModPair.adequacy_local_closed. econs; auto.
    2: { i. ss. split; ss; repeat (econs; eauto; ii; ss; des; clarify). }
    ii.
    eapply ModSemLPair.mk with (wf:=top1) (le:=top2); ss.
    econs; [|econs; [|econs;ss]].
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src.
      interp_red. steps. interp_red. steps. interp_red. steps.
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src.
      interp_red. steps. force_l. eexists. steps.
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src.
      interp_red. steps. force_l. eexists. steps.
  Qed.

  Lemma FG23_correct: Beh.of_program (ModL.compile FG2) <1= Beh.of_program (ModL.compile FG3).
  Proof.
    eapply ModPair.adequacy_local_closed. econs; auto.
    2: { i. ss. split; ss; repeat (econs; eauto; ii; ss; des; clarify). }
    ii.
    eapply ModSemLPair.mk with (wf:=top1) (le:=top2); ss.
    econs; [|econs; [|econs;ss]].
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src.
      interp_red. steps. interp_red. steps. interp_red. steps.
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src.
      interp_red. steps. force_l. eexists. steps.
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src.
      interp_red. steps. force_l. eexists. steps.
  Qed.

  Theorem FG_correct:
    Beh.of_program (Mod.compile FGImp) <1= Beh.of_program (Mod.compile FG3).
  Proof.
    i. eapply FG23_correct, FG12_correct, FG01_correct, FGImp0_correct, PR.
  Qed.

End PROOF.

Definition mutsum_imp := ModSemL.initial_itr_no_check (Mod.enclose FGImp).
Definition mutsum := ModSemL.initial_itr_no_check (Mod.enclose FG3).
