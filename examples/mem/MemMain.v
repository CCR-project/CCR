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





Arguments rel_dec_eq_true [T] eqt {r} {rc}.
(* rel_dec_eq_true =  *)
(* fun (T : Type) (eqt : T -> T -> Prop) (r : RelDec eqt) (rc : RelDec_Correct r) *)
(*   (x y : T) (H : eqt x y) => *)
(* let H0 : forall x0 y0 : T, eqt x0 y0 -> x0 ?[ eqt ] y0 = true := *)
(*   fun x0 y0 : T => match rel_dec_correct x0 y0 with *)
(*                    | conj _ x2 => x2 *)
(*                    end in *)
(* let H1 : x ?[ eqt ] y = true := H0 x y H in H1 *)
(*      : forall (T : Type) (eqt : T -> T -> Prop) (r : RelDec eqt), *)
(*        RelDec_Correct r -> forall x y : T, eqt x y -> x ?[ eqt ] y = true *)

(* Arguments rel_dec_eq_true [T]%type_scope [eqt]%function_scope [r] _ _ _ _ *)


Section WEAKENING.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Require Import Logic TODOYJ.


  Let weaken: forall (fn : string) (fsp_tgt : fspec),
      alist_find fn MemStb = Some fsp_tgt ->
      exists (fsp_src : fspec),
        (<< _ : alist_find fn (MemStb ++ MainStb) = Some fsp_src >>) /\ << _ : fspec_weaker fsp_tgt fsp_src >>
  .
  Proof.
    ii. stb_tac. des_ifs.
    - rewrite eq_rel_dec_correct in *. des_ifs. subst. esplits; eauto. { stb_tac. ss. } refl.
    - rewrite eq_rel_dec_correct in *. des_ifs. subst. esplits; eauto. { stb_tac. ss. } refl.
    - rewrite eq_rel_dec_correct in *. des_ifs. subst. esplits; eauto. { stb_tac. ss. } refl.
    - rewrite eq_rel_dec_correct in *. des_ifs. subst. esplits; eauto. { stb_tac. ss. } refl.
    - rewrite eq_rel_dec_correct in *. des_ifs. subst. esplits; eauto. { stb_tac. ss. } refl.
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

  (* Definition MemMain0: ModL.t := ModL.add Mem0.Mem Main0.Main. *)
  (* Definition MemMain1: ModL.t := ModL.add Mem1.Mem Main1.Main. *)
  (* Definition MemMain2: ModL.t := ModL.add (SMod.to_src Mem1.SMem) (SMod.to_src Main1.SMain). *)
  Definition MemMain0: ModL.t := Mod.add_list [Mem0.Mem; Main0.Main].
  Definition MemMain1: ModL.t := Mod.add_list [Mem1.Mem; Main1.Main].
  Definition MemMain2: ModL.t := Mod.add_list [(SMod.to_src Mem1.SMem); (SMod.to_src Main1.SMain)].

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

  Let sbtb_stb: (MemStb ++ MainStb) = List.map (fun '(gn, fsb) => (gn, fsb.(fsb_fspec))) (MemSbtb ++ MainSbtb).
  Proof. rewrite map_app. ss. unfold MainStb, MemStb. unseal "stb". refl. Qed.

  Let correct12: refines_closed MemMain1 MemMain2.
  Proof.
    set (global_sbtb:=MemSbtb++MainSbtb).
    Local Opaque MemSbtb.
    Local Opaque MainSbtb.
    unfold MemMain1, MemMain2.
    replace ([SMod.to_src SMem; SMod.to_src SMain]) with (List.map SMod.to_src [SMem; SMain]) by refl.
    eapply adequacy_type2; revgoals.
    { ss. right. left. unfold SMain. ss. }
    { instantiate (1:=ε). des_ifs. unfold compose. cbn.
      unfold ModSemL.initial_r_state in *. clarify. ss. repeat (try rewrite URA.unit_id; try rewrite URA.unit_idl).
      eapply GRA_wf_embed. eapply Auth_wf_black. repeat ur. i; ss. des_ifs.
    }
    { ss. }
    { set (skenv := Sk.load_skenv (fold_right Sk.add Sk.unit (List.map SMod.sk [SMem; SMain]))).
      econs.
      { esplits; cycle 1.
        { Fail Timeout 1 refl. (**************** FIXTHIS!!!!!!!!!!!!!!!!! ********************) unfold Mem. refl. }
        ii. ss. stb_tac.
        rewrite ! eq_rel_dec_correct in *. des_ifs; subst; esplits; try refl; et.
      }
      econs.
      { esplits; cycle 1.
        { Fail Timeout 1 refl. (**************** FIXTHIS!!!!!!!!!!!!!!!!! ********************) unfold Main. refl. }
        ii. ss. stb_tac. 
        rewrite ! eq_rel_dec_correct in *. des_ifs; subst; esplits; try refl; et.
      }
      econs.
    }
  Qed.

  Let correct01: refines_closed MemMain0 MemMain1.
  Proof.
    etrans; cycle 1.
    { instantiate (1:=ModL.add Mem0.Mem Main1.Main).
      eapply refines_close.
      hexploit (SimModSem.refines_proper_r [Mem1.Mem] [Mem0.Mem] [Main1.Main]).
      { cbn. rewrite ! ModL.add_empty_r. eapply SimModSem.adequacy_local.
        eapply Mem01proof.correct. }
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

  Theorem correct: refines_closed MemMain0 MemMain2.
  Proof.
    etrans. Fail Timeout 1 eauto. (************* FIXME!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *********)
    { eassumption. }
    { eapply correct12. }
  Qed.

End PROOF.
