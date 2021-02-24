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
Require Import MutF0 MutG0 MutMain0 MutF1 MutG1 MutMain1 MutF01proof MutG01proof MutMain01proof.

Require Import TODO.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Definition Σ: GRA.t := fun _ => URA.of_RA RA.empty.
  Local Existing Instance Σ.

  Local Opaque GRA.to_URA.
  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).

  Definition FG0: Mod.t := Mod.add_list [MutMain0.main ; MutF0.F ; MutG0.G].

  Definition FG1: Mod.t := Mod.add_list [MutMain1.main ; MutF1.F ; MutG1.G].

  Definition FG2: Mod.t := {|
    Mod.get_modsem := fun _ => {|
        ModSem.fnsems := List.map (fun '(fn, sb) => (fn, fun_to_src sb.(fsb_body))) (mainsbtb ++ (Fsbtb ++ Gsbtb));
        ModSem.initial_mrs := [("Main", (ε, tt↑)) ; ("F", (ε, tt↑)) ; ("G", (ε, tt↑))];
      |};
    Mod.sk := Sk.unit;
  |}
  .

  Definition FG3: Mod.t := {|
    Mod.get_modsem := fun _ => {|
        ModSem.fnsems := [("main", fun _ => Ret (Vint 55)↑) ; ("f", fun _ => triggerUB) ; ("g", fun _ => triggerUB)];
        ModSem.initial_mrs := [("Main", (ε, tt↑)) ; ("F", (ε, tt↑)) ; ("G", (ε, tt↑))];
      |};
    Mod.sk := Sk.unit;
  |}
  .

  Lemma FG01_correct: Beh.of_program (Mod.interp FG0) <1= Beh.of_program (Mod.interp FG1).
  Proof.
    eapply ModPair.sim_list_adequacy_closed. econs; [|econs; [|econs; ss]].
    - split; auto. ii. ss. eapply MutMain01proof.correct.
    - split; auto. ii. ss. eapply MutF01proof.correct.
    - split; auto. ii. ss. eapply MutG01proof.correct.
  Qed.

  Lemma FG12_correct: Beh.of_program (Mod.interp FG1) <1= Beh.of_program (Mod.interp FG2).
  Proof.
    ii.
    eapply adequacy_type with (sbtb:=mainsbtb++(Fsbtb++Gsbtb)) in PR; ss.
    cbn in *. unfold compose. ss. rewrite ! URA.unit_id. apply URA.wf_unit.
    Unshelve.
    all: try (by econs; ss).
  Qed.

  Lemma FG23_correct: Beh.of_program (Mod.interp FG2) <1= Beh.of_program (Mod.interp FG3).
  Proof.
    eapply ModPair.adequacy_local_closed. econs; auto. ii.
    eapply ModSemPair.mk with (wf:=top1) (le:=top2); ss.
    econs; [|econs; [|econs;ss]].
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src. steps.
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src. steps.
    - init. unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src. steps.
  Qed.

  Theorem FG_correct: Beh.of_program (Mod.interp FG0) <1= Beh.of_program (Mod.interp FG3).
  Proof.
    i. eapply FG23_correct, FG12_correct, FG01_correct, PR.
  Qed.

End PROOF.

Definition mutsum := ModSem.initial_itr (Mod.enclose FG3).
