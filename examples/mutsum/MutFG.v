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

  Definition FGImp: ModL.t := Mod.add_list [MutMain0.Main ; MutFImp.F ; MutGImp.G].

  Definition FG0: ModL.t := Mod.add_list [MutMain0.Main ; MutF0.F ; MutG0.G].

  Definition FG1: ModL.t := Mod.add_list [MutMain1.Main ; MutF1.F ; MutG1.G].

  Definition FG2: ModL.t :=
    Mod.add_list [
        SMod.to_src MutMain1.SMain;
        SMod.to_src MutF1.SF;
        SMod.to_src MutG1.SG
      ].

  Definition FG3: ModL.t := {|
    ModL.get_modsem := fun _ => {|
        ModSemL.fnsems :=
          [("main", fun _ => Ret (Vint 55)↑) ;
          ("f", fun _ => trigger (Choose _)) ;
          ("g", fun _ => trigger (Choose _))];
        ModSemL.initial_mrs := [("Main", (ε, tt↑)) ; ("F", (ε, tt↑)) ; ("G", (ε, tt↑))];
      |};
    ModL.sk := [("f", Sk.Gfun)] ++ [("g", Sk.Gfun)];
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
    - eapply MutMain01proof.correct.
    - eapply MutF01proof.correct.
    - eapply MutG01proof.correct.
  Qed.

  Lemma FG12_correct:
    refines_closed (FG1) (FG2).
  Proof.
    unfold FG1, FG2.
    replace [SMod.to_src SMain; SMod.to_src SF; SMod.to_src SG] with (List.map SMod.to_src [SMain; SF; SG]) by refl.
    { erewrite f_equal with (x:=[Main; F; G]).
      {
        eapply adequacy_type; revgoals.
        { ss. left. refl. }
        { instantiate (1:=ε). unfold compose. ss. rewrite ! URA.unit_id. apply URA.wf_unit. }
        { ss. }
      }
      refl.
    }
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
