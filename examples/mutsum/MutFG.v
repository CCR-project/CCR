Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import MutHeader.
Require Import MutF1 MutG1.

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

  Definition FG1: Mod.t := Mod.add F G.

  Definition FG2: Mod.t := {|
    Mod.get_modsem := fun _ => {|
        ModSem.fnsems := List.map (fun '(fn, sb) => (fn, fun_to_src sb.(fsb_body))) (Fsbtb ++ Gsbtb);
        ModSem.initial_mrs := [("F", (ε, unit↑)) ; ("G", (ε, unit↑))];
      |};
    Mod.sk := Sk.unit;
  |}
  .

  Local Opaque GRA.to_URA.
  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).
  Theorem correct: Beh.of_program (Mod.interp FG1) <1= Beh.of_program (Mod.interp FG2).
  Proof.
    ii.
    eapply adequacy_type with (sbtb:=Fsbtb++Gsbtb) in PR.
    { ss. }
    { ss. }
    { ss. admit "main - Fix me". }
    cbn in *. unfold compose. ss. rewrite ! URA.unit_id. apply URA.wf_unit.
  Unshelve.
    all: try (by econs; ss).
  Qed.









  Let ms: ModSem.t := {|
        ModSem.fnsems := List.map (fun '(fn, sb) => (fn, fun_to_src sb.(fsb_body))) (Fsbtb ++ Gsbtb);
        ModSem.initial_mrs := [];
  |}.

  (* Let itr0: callE ~> itree Es := fun _ ce => trigger PushFrame;; rv <- ModSem.sem ms ce;; trigger PopFrame;; Ret rv. *)
  (* Let itr1: itree (rE +' eventE) val := mrec itr0 (Call "main" []). *)
  (* Let itr2: itree eventE val := *)
  (*   assume (<<WF: ModSem.wf ms >>);; *)
  (*   snd <$> ModSem.interp_rE itr1 (ModSem.initial_r_state ms). *)

  (* Let itr0_nor: callE ~> itree Es := fun (T: Type) ce => (ModSem.sem ms ce): itree Es T. *)
  (* Let itr1_nor: itree (rE +' eventE) val := mrec itr0_nor (Call "main" []). *)

  (* Goal itr1_nor ≈ Ret (Vint (Z.of_nat 55)). *)
  (* Proof. *)
  (*   subst itr1_nor itr0_nor. ss. *)
  (*   (* rewrite mrec_as_interp. *) *)
  (*   unfold mrec. rewrite unfold_interp_mrec. ss. *)
  (*   ss. irw. rewrite tau_eutt. *)
  (*   unfold fun_to_src, body_to_src, interp_hCallE_src. *)
  (*   unfold mainBody. cbn. *)
  (* Abort. *)

End PROOF.
