Require Import sflib.
Require Import Universe.
Require Import Semantics.
Require Import Behavior.
From Paco Require Import paco.
Require Import RelationClasses List.
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.




Module Sim.
Section SIM.
  Variable L0 L1: semantics.
  Definition t: Type := forall (sim: L0.(state) -> L1.(state) -> Prop), L0.(state) -> L1.(state) -> Prop.

  Variable _sim: t.
  Variant _lift (lift: L0.(state) -> Beh.t): L0.(state) -> Beh.t :=
  | _lift_intro
      st_src0 st_tgt0 tr
      (SIM: _sim (fun st_src1 st_tgt1 => Beh.of_state L1 st_tgt1 <1= lift st_src1) st_src0 st_tgt0)
      (GIVEN: Beh.of_state L1 st_tgt0 tr)
    :
      _lift lift st_src0 tr
  .
  Hint Constructors _lift.

  Lemma lift_mon (MON: monotone2 _sim): monotone2 _lift.
  Proof.
    ii. inv IN. econs; eauto.
  Qed.

  Definition lift := paco2 _lift bot2.

End SIM.
End Sim.
Hint Constructors Sim._lift.
Hint Unfold Sim.lift.
Hint Resolve Sim.lift_mon: paco.



Module Simple.
  Section SIM.
    Variable L0 L1: semantics.
    Definition bsim (sim: L0.(state) -> L1.(state) -> Prop): L0.(state) -> L1.(state) -> Prop :=
      fun st_src0 st_tgt0 =>
        match L0.(state_sort) st_src0, L1.(state_sort) st_tgt0 with
        | angelic, angelic =>
          forall st_src1 ev (STEPSRC: L0.(step) st_src0 ev st_src1),
          exists st_tgt1, (<<STEPTGT: L1.(step) st_tgt0 ev st_tgt1>>) /\ (<<SIM: sim st_src1 st_tgt1>>)
        | demonic, demonic =>
          forall st_tgt1 ev (STEPTGT: L1.(step) st_tgt0 ev st_tgt1),
          exists st_src1, (<<STEPSRC: L0.(step) st_src0 ev st_src1>>) /\ (<<SIM: sim st_src1 st_tgt1>>)
        | final, final => False
        | _, _ => False
        end
    .

    Theorem bsim_mon: monotone2 bsim.
    Proof.
      ii. r. r in IN. des_ifs; ss; et.
      - ii. exploit IN; eauto. i; des. eauto.
      - ii. exploit IN; eauto. i; des. eauto.
    Qed.

    (* Theorem bsim_compat: compatible2 (Beh._of_state L0) (Sim._lift L0 L1 bsim). *)
    (* Proof. *)
    (*   econs. *)
    (*   { eapply Sim.lift_mon; eauto. eapply bsim_mon; eauto. } *)
    (* Admitted. *)

    Theorem bsim_spec:
      (Sim._lift L0 L1 bsim) <3= gupaco2 (Beh._of_state L0) (cpn2 (Beh._of_state L0)).
    Proof.
      gcofix CIH. intros. destruct PR.
      r in SIM. des_ifs.
      - gstep. econs 7; et. rr. ii.
        esplits; eauto. exploit SIM; eauto. i; des.
        exploit SIM0; eauto. intro A.
        destruct ev; ss.
        + destruct e; ss. right.
          esplits; eauto.
          { gfinal; eauto. }
          admit.
        + left. esplits; eauto. admit.
      - admit.
    Admitted.

  End SIM.

  (* Inductive bindC (r: itr_src -> itr_tgt -> Prop) : itr_src -> itr_tgt -> Prop := *)
  (* | bindC_intro *)
  (*     i_src i_tgt *)
  (*     (SIM: match_itr i_src i_tgt) *)
  (*     k_src k_tgt *)
  (*     (SIMK: HProper (SALL !-> r) k_src k_tgt) *)
  (*   : *)
  (*     bindC r (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt) *)
  (* . *)

  (* Hint Constructors bindC: core. *)

  (* Lemma bindC_spec *)
  (*       simC *)
  (*   : *)
  (*     bindC <3= gupaco2 (_match_itr) (simC) *)
  (* . *)
  (* Proof. *)
  (*   gcofix CIH. intros. destruct PR. *)
  (*   punfold SIM. inv SIM. *)
  (*   - rewrite ! bind_ret_l. gbase. eapply SIMK; et. rr; et. *)
  (*   - rewrite ! bind_tau. gstep. econs; eauto. pclearbot. *)
  (*     (* gfinal. left. eapply CIH. econstructor; eauto. *) *)
  (*     debug eauto with paco. *)
  (*   - rewrite ! bind_vis. gstep. econs; eauto. u. ii. repeat spc MATCH. pclearbot. eauto with paco. *)
  (*   - rewrite ! bind_vis. gstep. econs; eauto. u. ii. repeat spc MATCH. pclearbot. *)
  (*     eauto with paco. *)
  (*   - rewrite ! bind_vis. gstep. econs; eauto. *)
  (*   - rewrite ! bind_vis. gstep. econs; eauto. *)
  (*   - rewrite ! bind_vis. *)
  (*     gstep. econs; eauto. ii. exploit SIM0; et. intro T; des_safe. pclearbot. eauto with paco. *)
  (*   - rewrite ! bind_vis. rewrite ! bind_tau. *)
  (*     gstep. econs; eauto. des. pclearbot. eauto with paco. *)
  (*   - rewrite ! bind_vis. rewrite ! bind_tau. *)
  (*     gstep. econs; eauto. ii. pclearbot. eauto with paco. *)
  (* Qed. *)

  (* gpaco2 _match_itr (cpn2 _match_itr) bot2 bot2 (` x : _ <- a2;; a0 x) (` x : _ <- a3;; a1 x) *)

  (* gpaco2 (Beh._of_state L0) (cpn2 (Beh._of_state L0)) bot2 r (initial_state L0) tr *)

End Simple.



Theorem compsim_compat
        L0 L1
  :
    Beh.improves (Beh.of_program L0) (Beh.of_program L1)
.
Proof.
  unfold Beh.of_program.
  r.
  ginit.
  { i. eapply cpn2_wcompat; eauto. eapply Beh.of_state_mon. }
  gcofix CIH. i. rename x2 into tr.
  - guclo Simple.bsim_spec.
    econs; eauto.
    r. des_ifs.
    ii.
    apply gpaco2_gupaco; eauto.
    { eapply Beh.of_state_mon. }
    eapply Simple.bsim_compat.

    guclo Simple.bsim_compat. gclo. Set Printing All. Compute (fun _ : state L0 => Tr.t).
Qed.
