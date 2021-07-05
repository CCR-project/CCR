Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
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

  Lemma FGImp0_correct:
    refines FGImp FG0.
  Proof.
    eapply adequacy_local_list. econs; [|econs; [|econs; ss]].
    - econs; ss. ii. eapply ModSemPair.self_sim.
    - split; auto. ii. ss. eapply MutFImp0proof.correct.
    - split; auto. ii. ss. eapply MutGImp0proof.correct.
  Qed.

  Lemma FG01_correct:
    refines FG0 FG1.
  Proof.
    eapply adequacy_local_list. econs; [|econs; [|econs; ss]].
    - eapply MutMain01proof.correct.
    - eapply MutF01proof.correct.
    - eapply MutG01proof.correct.
  Qed.

  Require Import ProofMode.

  Lemma FG12_correct:
    refines_closed (FG1) (FG2).
  Proof.
    unfold FG1, FG2.
    replace [SMod.to_src SMain; SMod.to_src SF; SMod.to_src SG] with (List.map SMod.to_src [SMain; SF; SG]) by refl.
    erewrite f_equal with (x:=[Main; F; G]).
    { eapply adequacy_type with (stb:=fun _ => GlobalStb); et.
      { instantiate (1:=ε). ss. rewrite ! URA.unit_id. eapply URA.wf_unit. }
      i. cbn in MAIN. ss. des_ifs. exists tt. split.
      { iIntros "H". ss. }
      { ii. iPureIntro. i. des. auto. }
    }
    { ss. }
  Qed.

  Definition F3: Mod.t := {|
    Mod.get_modsem := fun _ => {|
      ModSem.fnsems := [("f", fun _ => trigger (Choose _))];
      ModSem.mn := "F";
      ModSem.initial_st := tt↑;
    |};
    Mod.sk := [("f", Sk.Gfun)];
  |}
  .

  Definition G3: Mod.t := {|
    Mod.get_modsem := fun _ => {|
      ModSem.fnsems := [("g", fun _ => trigger (Choose _))];
      ModSem.mn := "G";
      ModSem.initial_st := tt↑;
    |};
    Mod.sk := [("g", Sk.Gfun)];
  |}
  .

  Definition Main3: Mod.t := {|
    Mod.get_modsem := fun _ => {|
      ModSem.fnsems := [("main", fun _ => Ret (Vint 55)↑)];
      ModSem.mn := "Main";
      ModSem.initial_st := tt↑;
    |};
    Mod.sk := Sk.unit;
  |}
  .

  Definition FG3: ModL.t := Mod.add_list [Main3;F3;G3].

  Lemma FG23_correct: refines_closed (FG2) (FG3).
  Proof.
    eapply refines_close.
    eapply adequacy_local_list. econs; [|econs; [|econs; ss]].
    - econs; ss. ii. econstructor 1 with (wf:=top2) (le:=top2); ss. econs; et.
      init. unfold cfunN, fun_to_src, body_to_src, mainBody. steps.
    - econs; ss. ii. econstructor 1 with (wf:=top2) (le:=top2); ss. econs; et.
      init. unfold cfunN, fun_to_src, body_to_src, mainBody. steps.
      force_l. eexists. steps.
    - econs; ss. ii. econstructor 1 with (wf:=top2) (le:=top2); ss. econs; et.
      init. unfold cfunN, fun_to_src, body_to_src, mainBody. steps.
      force_l. eexists. steps.
      Unshelve. all: try (exact tt).
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

Definition mutsum_imp := ModSemL.initial_itr (ModL.enclose FGImp) None.
Definition mutsum := ModSemL.initial_itr (ModL.enclose FG3) None.
