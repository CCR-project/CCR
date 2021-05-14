Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare Open OpenDef.
Require Import Weakening.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Require Import Mem0 Mem1 MemOpen Mem0Openproof.
Require Import Main0 Main1 Main01proof.





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



Require Import Open.

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Variable _ctxs: list UMod.t.
  Let ctxs := List.map UMod.to_mod _ctxs.

  Definition MemMain0 := Mod.add_list ([Mem0.Mem; Main0.Main] ++ ctxs).
  Definition MemMain1 := Mod.add_list ([MemOpen.Mem; Main1.Main] ++ ctxs).
  Definition MemMain2 := Mod.add_list ([KMod.to_src MemOpen.KMem; SMod.to_src Main1.SMain] ++ ctxs).

  Let sbtb_stb: (MemStb ++ MainStb) = List.map (fun '(gn, fsb) => (gn, fsb.(fsb_fspec))) (MemSbtb ++ MainSbtb).
  Proof. rewrite map_app. ss. unfold MainStb, MemStb. unseal "stb". refl. Qed.

  Let TODO_REMOVE_THIS: SimModSem.ModPair.sim MemOpen.Mem Mem0.Mem.
  Proof.
    econs.
    { ii. eapply SimModSem.adequacy_lift.
      replace (Mod.get_modsem Mem0.Mem sk) with (Mem0.MemSem sk) by refl.
      replace (Mod.get_modsem MemOpen.Mem sk) with (MemOpen.MemSem sk) by refl.
      eapply Mem0Openproof.correct.
    }
    { ss. }
    { ii. repeat (econs; ss; ii; des; ss). }
  Qed.

  Let correct01: refines_closed MemMain0 MemMain1.
  Proof.
    etrans; cycle 1.
    { instantiate (1:=Mod.add_list ([Mem0.Mem; Main1.Main] ++ ctxs)).
      eapply refines_close.
      unfold MemMain1. rewrite ! Mod.add_list_app. eapply (SimModSem.refines_proper_r).
      hexploit (SimModSem.refines_proper_r [MemOpen.Mem] [Mem0.Mem] [Main1.Main]).
      { cbn. rewrite ! ModL.add_empty_r. eapply SimModSem.adequacy_local. eapply TODO_REMOVE_THIS. }
      intro T; des. cbn in T. rewrite ! ModL.add_empty_r in T. ss.
    }
    etrans; cycle 1.
    { instantiate (1:=Mod.add_list ([Mem0.Mem; Main0.Main] ++ ctxs)).
      eapply refines_close.
      rewrite ! Mod.add_list_app. eapply (SimModSem.refines_proper_r).
      hexploit (SimModSem.refines_proper_l [Main1.Main] [Main0.Main] [Mem0.Mem]).
      { cbn. rewrite ! ModL.add_empty_r. eapply SimModSem.adequacy_local.
        eapply Main01proof.correct.
      }
      intro T; des. cbn in T. rewrite ! ModL.add_empty_r in T. ss.
    }
    refl.
  Qed.

  Let _kmds: list KMod.t := [KMem].
  Let correct12: refines_closed MemMain1 MemMain2.
  Proof.
    rp; [eapply (adequacy_open _kmds _ctxs)|..]; revgoals.
    { unfold MemMain2. repeat f_equal. unfold _kmds. unfold SMem. cbn.
      f_equal.
      admit "TODO: do better with main".
    }
    { unfold MemMain1. repeat f_equal.
      rewrite List.map_map. unfold _kmds. Opaque KMem. cbn. unfold Mem. unfold SMem.
      replace (fun ske : Sk.t =>
      (List.map (map_snd fsb_fspec)
         (List.map (map_snd disclose_fsb) (List.map (map_snd KModSem.transl_fsb) (KModSem.fnsems (KMod.get_modsem KMem ske)))) ++ []) ++
      flat_map (List.map (map_snd (fun _ : list val -> itree (callE +' pE +' eventE) val => fspec_trivial2)) ∘ UModSem.fnsems)
        (List.map (flip UMod.get_modsem ske) _ctxs)) with (fun (_: Sk.t) => []: list (string * fspec)); cycle 1.
      { admit "ez - weakening". }
      f_equal.
      admit "TODO: do better with main".
    }
    { admit "TODO: do better with main". }
    { admit "TODO: do better with main". }
  Unshelve.
  { apply URA.unit. }
  { ii. apply True. }
  { ii. apply ITree.spin. }
  Qed.

End PROOF.

