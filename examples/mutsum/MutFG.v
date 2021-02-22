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











Hint Rewrite unfold_interp_mrec : itree_axiom2.
Hint Rewrite bind_ret_l : itree_axiom2.
Hint Rewrite bind_ret_r : itree_axiom2.
Hint Rewrite bind_tau : itree_axiom2.
Hint Rewrite bind_vis : itree_axiom2.
(* Hint Rewrite bind_trigger : itree_axiom. *)
Hint Rewrite bind_bind : itree_axiom2.
Tactic Notation "irw" "in" ident(H) := repeat (autorewrite with itree_axiom2 in H; cbn in H).
Tactic Notation "irw" := repeat (autorewrite with itree_axiom2; cbn).










Section PROOF.

  Context `{Σ: GRA.t}.
  Local Opaque GRA.to_URA.
  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).

  Definition FG0: Mod.t := add_list [MutMain0.main ; MutF0.F ; MutG0.G].

  Definition FG1: Mod.t := add_list [MutMain1.main ; MutF1.F ; MutG1.G].

  Definition FG2: Mod.t := {|
    Mod.get_modsem := fun _ => {|
        ModSem.fnsems := List.map (fun '(fn, sb) => (fn, fun_to_src sb.(fsb_body))) (mainsbtb ++ (Fsbtb ++ Gsbtb));
        ModSem.initial_mrs := [("Main", (ε, unit↑)) ; ("F", (ε, unit↑)) ; ("G", (ε, unit↑))];
      |};
    Mod.sk := Sk.unit;
  |}
  .

  Definition FG3: Mod.t := {|
    Mod.get_modsem := fun _ => {|
        ModSem.fnsems := [("main", fun _ => Ret (Vint 55)↑) ; ("f", fun _ => triggerUB) ; ("g", fun _ => triggerUB)];
        ModSem.initial_mrs := [("Main", (ε, unit↑)) ; ("F", (ε, unit↑)) ; ("G", (ε, unit↑))];
      |};
    Mod.sk := Sk.unit;
  |}
  .

  Lemma FG01_correct: Beh.of_program (Mod.interp FG0) <1= Beh.of_program (Mod.interp FG1).
  Proof.
    eapply sim_list_adequacy_closed. econs; [|econs; [|econs; ss]].
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
    eapply adequacy_local_closed. econs; auto. ii.
    eapply ModSemPair.mk with (wf:=top1) (le:=top2); ss.
    econs; [|econs; [|econs;ss]].
    - econs; ss. ii. subst. exists 100.
      unfold fun_to_src, cfun, body_to_src, mainBody, interp_hCallE_src, unwrapN, triggerNB.
      ired. des_ifs.
      + ired. repeat rewrite interp_trigger. ired.
        pfold. econs; eauto. i. left.
        pfold. ired. econs; eauto. left.
        pfold. econs; eauto.
      + ired. pfold. econs; eauto. ss.
    - econs; ss. ii. subst. exists 100.
      ss. pfold. econs; ss.
    - econs; ss. ii. subst. exists 100.
      ss. pfold. econs; ss.
  Qed.

  Theorem FG_correct: Beh.of_program (Mod.interp FG0) <1= Beh.of_program (Mod.interp FG3).
  Proof.
    i. eapply FG23_correct, FG12_correct, FG01_correct, PR.
  Qed.

End PROOF.
