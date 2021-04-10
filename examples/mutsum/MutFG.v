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




Section AUX.

  Context `{Σ: GRA.t}.

  Definition refines_closed (md_tgt md_src: ModL.t): Prop :=
    Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_src)
  .

  Lemma refines_close: SimModSem.refines <2= refines_closed.
  Proof. ii. specialize (PR nil). ss. unfold Mod.add_list in *. ss. rewrite ! ModL.add_empty_l in PR. eauto. Qed.

  Definition add_list (ms: list ModL.t): ModL.t := fold_right ModL.add ModL.empty ms.

  Global Program Instance refines_closed_PreOrder: PreOrder refines_closed.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. r in H. r in H0. eauto. Qed.

End AUX.

Section PROOF.

  Definition Σ: GRA.t := fun _ => of_RA.t RA.empty.
  Local Existing Instance Σ.

  Definition FGImp: ModL.t := Mod.add_list [MutMain0.main ; MutFImp.F ; MutGImp.G].

  Definition FG0: ModL.t := Mod.add_list [MutMain0.main ; MutF0.F ; MutG0.G].

  Definition FG1: ModL.t := Mod.add_list [MutMain1.main ; MutF1.F ; MutG1.G].

  Definition FG2: ModL.t :=
    add_list [
        md_src MutMain1.main mainsbtb ; (* Main *)
        md_src MutF1.F Fsbtb ;  (* F *)
        md_src MutG1.G Gsbtb  (* G *)
      ].

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
    refines_closed (FG1) (FG2).
  Proof.
    ii.
    eapply adequacy_type with (sbtb:=mainsbtb++(Fsbtb++Gsbtb)) in PR; ss.
    instantiate (1:=ε).
    cbn in *. unfold compose. ss. rewrite ! URA.unit_id. apply URA.wf_unit.
    Unshelve.
    all: try (by econs; ss).
  Qed.

  (* Definition F3: Mod.t := {| *)
  (*   Mod.get_modsem := fun _ => {| *)
  (*     ModSem.fnsems := [("f", fun _ => trigger (Choose _))]; *)
  (*     ModSem.mn := "F"; *)
  (*     ModSem.initial_mr := ε; *)
  (*     ModSem.initial_st := tt↑; *)
  (*   |}; *)
  (*   Mod.sk := Sk.unit; *)
  (* |} *)
  (* . *)

  (* Definition G3: Mod.t := {| *)
  (*   Mod.get_modsem := fun _ => {| *)
  (*     ModSem.fnsems := [("g", fun _ => trigger (Choose _))]; *)
  (*     ModSem.mn := "G"; *)
  (*     ModSem.initial_mr := ε; *)
  (*     ModSem.initial_st := tt↑; *)
  (*   |}; *)
  (*   Mod.sk := Sk.unit; *)
  (* |} *)
  (* . *)

  (* Definition Main3: Mod.t := {| *)
  (*   Mod.get_modsem := fun _ => {| *)
  (*     ModSem.fnsems := [("main", fun _ => trigger (Choose _))]; *)
  (*     ModSem.mn := "Main"; *)
  (*     ModSem.initial_mr := ε; *)
  (*     ModSem.initial_st := tt↑; *)
  (*   |}; *)
  (*   Mod.sk := Sk.unit; *)
  (* |} *)
  (* . *)

  (*** TODO: we can generalize adequacy_type, so that FG2 is defined as a summation of Mod.t, NOT ModL.t.
Then, we can just use SimModSem.adequacy_local_list. in this proof (FG23_correct).
   ***)
  Lemma FG23_correct: refines_closed (FG2) (FG3).
  Proof.
    r. eapply ModLPair.adequacy_local_closed. econs; auto.
    2: { i. ss. split; ss; repeat (econs; eauto; ii; ss; des; clarify). }
    ii.
    eapply ModSemLPair.mk with (wf:=top1) (le:=top2); ss.
    econs; [|econs; [|econs;ss]].
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src, compose.
      admit "ez; interp_red. steps. interp_red. steps. interp_red. steps".
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src.
      admit "ez; interp_red. steps. force_l. eexists. steps".
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src.
      admit "ez; interp_red. steps. force_l. eexists. steps".
  Qed.

  Theorem FG_correct:
    refines_closed FGImp FG3.
  Proof.
    etrans.
    { eapply refines_close. eapply FGImp0_correct. }
    etrans.
    { eapply refines_close. eapply FG01_correct. }
    etrans.
    { eapply FG12_correct. }
    etrans.
    { eapply FG23_correct. }
    refl.
  Qed.

End PROOF.

Definition mutsum_imp := ModSemL.initial_itr_no_check (ModL.enclose FGImp).
Definition mutsum := ModSemL.initial_itr_no_check (ModL.enclose FG3).
