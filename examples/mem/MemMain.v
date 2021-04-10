Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import Weakening.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Require Import Mem0 Mem1 Mem01proof Main0 Main1.




Section AUX________REMOVEME_____REDUNDANT.

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

End AUX________REMOVEME_____REDUNDANT.




Module Mem2.
Section MEM2.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition MemSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt (MemStb ++ MainStb) fn fsb)) MemSbtb;
    ModSem.mn := "Mem";
    ModSem.initial_mr := (GRA.embed (Auth.black (M:=Mem1._memRA) ε));
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Mem: Mod.t := {|
    Mod.get_modsem := fun _ => MemSem;
    Mod.sk := Sk.unit;
  |}
  .

End MEM2.
End Mem2.




Section WEAKENING.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Require Import Logic TODOYJ.
  Let weaken: forall (fn fn_tgt : string) (fsp_tgt : fspec),
      find (fun '(_fn, _) => dec fn _fn) MemStb = Some (fn_tgt, fsp_tgt) ->
      exists (fn_src : string) (fsp_src : fspec),
        (<< _ : find (fun '(_fn, _) => dec fn _fn) (MemStb ++ MainStb) = Some (fn_src, fsp_src) >>) /\ << _ : fspec_weaker fsp_tgt fsp_src >>
  .
  Proof.
    ii. stb_tac. des_ifs.
    - des_sumbool. subst. esplits; eauto. { stb_tac. ss. } refl.
    - des_sumbool. subst. esplits; eauto. { stb_tac. ss. } refl.
    - des_sumbool. subst. esplits; eauto. { stb_tac. ss. } refl.
    - des_sumbool. subst. esplits; eauto. { stb_tac. ss. } refl.
    - des_sumbool. subst. esplits; eauto. { stb_tac. ss. } refl.
  Qed.

  Theorem Mem12correct: SimModSem.ModSemPair.sim Mem2.MemSem Mem1.MemSem.
  Proof.
    econs.
    { econs.
      { r. split.
        { cbn. unfold RelationPairs.RelCompFun. cbn. refl. }
        eapply weakening_fn; try refl.
        { eapply weaken. }
      }
      econs.
      { r. split.
        { cbn. unfold RelationPairs.RelCompFun. cbn. refl. }
        eapply weakening_fn; try refl.
        { eapply weaken. }
      }
      econs.
      { r. split.
        { cbn. unfold RelationPairs.RelCompFun. cbn. refl. }
        eapply weakening_fn; try refl.
        { eapply weaken. }
      }
      econs.
      { r. split.
        { cbn. unfold RelationPairs.RelCompFun. cbn. refl. }
        eapply weakening_fn; try refl.
        { eapply weaken. }
      }
      econs.
      { r. split.
        { cbn. unfold RelationPairs.RelCompFun. cbn. refl. }
        eapply weakening_fn; try refl.
        { eapply weaken. }
      }
      econs.
    }
    { ss. }
    { ss. esplits; eauto. }
  Qed.

End WEAKENING.





Section AUX.

  Theorem GRA_wf_embed
          A
          `{@GRA.inG A Σ}
          (a: A)
          (WF: URA.wf a)
    :
      URA.wf (GRA.embed a)
  .
  Proof.
    ss. ii. unfold GRA.embed.
    Local Transparent GRA.to_URA. ur. i. des_ifs; cycle 1.
    { apply URA.wf_unit. }
    ss. unfold PCM.GRA.cast_ra, eq_rect, eq_sym. destruct GRA.inG_prf. ss.
    Local Opaque GRA.to_URA.
  Qed.

  Theorem Auth_wf_black
          `{M: URA.t}
          a
          (WF: URA.wf a)
    :
      <<WF: URA.wf (Auth.black a)>>
  .
  Proof. ur. split; ss. r. esplits. rewrite URA.unit_idl. refl. Qed.

End AUX.




Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition MemMain0: ModL.t := ModL.add Mem0.Mem Main0.Main.
  Definition MemMain1: ModL.t := ModL.add Mem2.Mem Main1.Main.

  (* Definition MainSem2: ModSemL.t := {| *)
  (*   ModSemL.fnsems := List.map (map_snd fun_to_src) MainStb; *)
  (*   ModSemL.initial_mrs := [("Main", ε)]; *)
  (* |} *)
  (* . *)

  (* Definition Main2: Mod.t := {| *)
  (*   Mod.get_modsem := fun _ => MainSem2; *)
  (*   Mod.sk := Sk.unit; *)
  (* |} *)
  (* . *)

  (* Definition MemSem2: ModSemL.t := {| *)
  (*   ModSemL.fnsems := List.map (map_snd fun_to_src) MemStb; *)
  (*   ModSemL.initial_mrs := [("Mem", ε)]; *)
  (* |} *)
  (* . *)

  (* Definition Mem2: Mod.t := {| *)
  (*   Mod.get_modsem := fun _ => MemSem2; (*** TODO: we need proper handling of function pointers ***) *)
  (*   Mod.sk := Sk.unit; *)
  (* |} *)
  (* . *)

  (* Definition MemMain2: Mod.t := Mod.add Mem2 Main2. *)

  Definition MemMain2: ModL.t := {|
    ModL.get_modsem := fun _ => {|
        ModSemL.fnsems := List.map (fun '(fn, sb) => (fn, (transl_all sb.(fsb_fspec).(mn)) <*> fun_to_src sb.(fsb_body))) (MemSbtb ++ MainSbtb);
        (* ModSemL.initial_mrs := [("Mem", ε) ; ("Main", ε)]; *)
        ModSemL.initial_mrs := [("Mem", (ε, tt↑)) ; ("Main", (ε, tt↑))];
      |};
    ModL.sk := Sk.unit;
  |}
  .

  Let sbtb_stb: (MemStb ++ MainStb) = List.map (fun '(gn, fsb) => (gn, fsb.(fsb_fspec))) (MemSbtb ++ MainSbtb).
  Proof. rewrite map_app. ss. unfold MainStb, MemStb. unseal "stb". refl. Qed.

  Theorem correct12: refines_closed MemMain1 MemMain2.
  Proof.
    r.
    set (global_sbtb:=MemSbtb++MainSbtb).
    Local Opaque MemSbtb.
    Local Opaque MainSbtb.
    eapply adequacy_type with (sbtb:=global_sbtb).
    { seal fun_to_tgt. unfold compose. cbn. unfold global_sbtb. rewrite map_app. unfold ModSem.map_snd.
      f_equal.
      - rewrite List.map_map. eapply map_ext. ii. des_ifs. r. f_equal. apply func_ext. i. f_equal.
        + Local Transparent MemSbtb. cbn in IN. Local Opaque MemSbtb.
          des; ss; clarify; ss.
        + unseal fun_to_tgt. f_equal. ss.
      - rewrite List.map_map. eapply map_ext. ii. des_ifs. r. f_equal. apply func_ext. i. f_equal.
        + Local Transparent MainSbtb. cbn in IN. Local Opaque MainSbtb.
          des; ss; clarify; ss.
        + unseal fun_to_tgt. f_equal. ss.
    }
    { ss. }
    { ss. }
    { instantiate (1:=ε). des_ifs. ss. unfold compose, ModSemL.initial_r_state in *. des_ifs.
      rewrite ! URA.unit_idl. ss. rewrite ! URA.unit_id. eapply GRA_wf_embed. eapply Auth_wf_black.
      repeat ur. i; ss.
    }
  Qed.

  Theorem correct: refines_closed MemMain0 MemMain2.
  Proof.
    etrans; cycle 1.
    { eapply correct12. }
    etrans; cycle 1.
    { instantiate (1:=ModL.add Mem1.Mem Main1.Main).
      eapply refines_close.
      hexploit (SimModSem.refines_proper_r [Mem2.Mem] [Mem1.Mem] [Main1.Main]).
      { cbn. rewrite ! ModL.add_empty_r. eapply SimModSem.adequacy_local.
        econs.
        - i. cbn. eapply SimModSem.adequacy_lift. eapply Mem12correct.
        - ss.
        - cbn. ii. rr. econs; ss.
          { repeat (econs; ii; ss; des; ss). }
          { repeat (econs; ii; ss; des; ss). }
      }
      intro T; des. cbn in T. rewrite ! ModL.add_empty_r in T. ss.
    }
    etrans; cycle 1.
    { instantiate (1:=ModL.add Mem0.Mem Main1.Main).
      eapply refines_close.
      hexploit (SimModSem.refines_proper_r [Mem1.Mem] [Mem0.Mem] [Main1.Main]).
      { cbn. rewrite ! ModL.add_empty_r. eapply SimModSem.adequacy_local.
        econs.
        - i. cbn. eapply SimModSem.adequacy_lift. eapply Mem01proof.correct.
        - ss.
        - cbn. ii. rr. econs; ss.
          { repeat (econs; ii; ss; des; ss). }
          { repeat (econs; ii; ss; des; ss). }
      }
      intro T; des. cbn in T. rewrite ! ModL.add_empty_r in T. ss.
    }
    etrans; cycle 1.
    { instantiate (1:=ModL.add Mem0.Mem Main0.Main).
      eapply refines_close.
      hexploit (SimModSem.refines_proper_l [Main1.Main] [Main0.Main] [Mem0.Mem]).
      { cbn. rewrite ! ModL.add_empty_r. eapply SimModSem.adequacy_local.
        econs.
        - i. cbn. eapply SimModSem.adequacy_lift. admit "should be ez".
        - ss.
        - cbn. ii. rr. econs; ss.
          { repeat (econs; ii; ss; des; ss). }
          { repeat (econs; ii; ss; des; ss). }
      }
      intro T; des. cbn in T. rewrite ! ModL.add_empty_r in T. ss.
    }
    refl.
  Qed.

End PROOF.
