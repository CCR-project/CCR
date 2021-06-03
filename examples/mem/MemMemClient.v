Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare Open OpenDef.
Require Import SimModSem Weakening.

Set Implicit Arguments.



Require Import Mem0 Mem1 MemOpen Mem0Openproof MemClient0 MemClient1 MemClient01proof.





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


Section WEAKENINGAUX.
  Context `{Σ: GRA.t}.

  Definition stb_le (stb0 stb1: list (string * fspec)) :=
    forall fn fsp0 (FINDTGT: alist_find fn stb0 = Some (fsp0)),
    exists fsp1,
      (<<FINDSRC: alist_find fn stb1 = Some (fsp1)>>) /\
      (<<WEAKER: fspec_weaker fsp0 fsp1>>)
  .

  Variable md: (Sk.t -> list (string * fspec)) -> Mod.t.
  Variable _stb0 _stb1: (Sk.t -> list (string * fspec)).
  Hypothesis WEAKEN: forall sk, stb_le (_stb0 sk) (_stb1 sk).

  Theorem adequacy_weaken
          sk
    :
      <<SIM: ModSemPair.sim (Mod.get_modsem (md _stb0) sk) (Mod.get_modsem (md _stb1) sk)>>
  .
  Proof.
    TTTTTTTTTTTTTTTTTTTTTTTTTTTT
  Qed.

End WEAKENINGAUX.

Section WEAKENING.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Require Import Logic TODOYJ.


  Let weaken: forall (fn : string) (fsp_tgt : fspec),
      alist_find fn MemStb = Some fsp_tgt ->
      exists (fsp_src : fspec),
        (<< _ : alist_find fn (MemStb ++ ClientStb) = Some fsp_src >>) /\ << _ : fspec_weaker fsp_tgt fsp_src >>
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

  Let global_stb sk :=
    MemStb ++ ClientStb ++
    flat_map (map (map_snd (λ _, fspec_trivial2)) ∘ UModSem.fnsems) (map (flip UMod.get_modsem sk) _ctxs).

  Definition MemClient0 := Mod.add_list ([Mem0.Mem; MemClient0.Client] ++ ctxs).
  Definition MemClient1 :=
    Mod.add_list ([MemOpen.Mem (fun _ => []);
                  MemClient1.Client (fun _ => (UnknownStb ++ ClientStb ++ MemStb))] ++ ctxs).
  Definition MemClient2 := Mod.add_list ([MemOpen.Mem global_stb; MemClient1.Client global_stb] ++ ctxs).
  Definition MemClient3 := Mod.add_list ([KMod.to_src MemOpen.KMem; KMod.to_src MemClient1.KClient] ++ ctxs).

  Let TODO_REMOVE_THIS: SimModSem.ModPair.sim (MemOpen.Mem (fun _ => [])) Mem0.Mem.
  Proof.
    econs.
    { ii. eapply SimModSem.adequacy_lift.
      replace (Mod.get_modsem Mem0.Mem sk) with (Mem0.MemSem sk) by refl.
      replace (Mod.get_modsem (MemOpen.Mem (fun _ => [])) sk) with (MemOpen.MemSem [] sk) by refl.
      eapply Mem0Openproof.correct.
    }
    { ss. }
    { ii. repeat (econs; ss; ii; des; ss). }
  Qed.

  Let correct01: refines_closed MemClient0 MemClient1.
  Proof.
    etrans; cycle 1.
    { instantiate (1:=Mod.add_list ([Mem0.Mem; MemClient1.Client (fun _ => (UnknownStb ++ ClientStb ++ MemStb))] ++ ctxs)).
      eapply refines_close.
      unfold MemClient1. rewrite ! Mod.add_list_app. eapply (SimModSem.refines_proper_r).
      hexploit (SimModSem.refines_proper_r [MemOpen.Mem (fun _ => [])] [Mem0.Mem]
                                           [MemClient1.Client (fun _ => (UnknownStb ++ ClientStb ++ MemStb))]).
      { cbn. rewrite ! ModL.add_empty_r. eapply SimModSem.adequacy_local. eapply TODO_REMOVE_THIS. }
      intro T; des. cbn in T. rewrite ! ModL.add_empty_r in T. ss.
    }
    etrans; cycle 1.
    { instantiate (1:=Mod.add_list ([Mem0.Mem; MemClient0.Client] ++ ctxs)).
      eapply refines_close.
      rewrite ! Mod.add_list_app. eapply (SimModSem.refines_proper_r).
      hexploit (SimModSem.refines_proper_l [MemClient1.Client (fun _ => (UnknownStb ++ ClientStb ++ MemStb))]
                                           [MemClient0.Client] [Mem0.Mem]).
      { cbn. rewrite ! ModL.add_empty_r. eapply SimModSem.adequacy_local.
        eapply MemClient01proof.correct.
      }
      intro T; des. cbn in T. rewrite ! ModL.add_empty_r in T. ss.
    }
    refl.
  Qed.

  Let mem_sbtb_stb: (MemStb) = (List.map (map_snd (fun ksb => (KModSem.disclose_ksb ksb): fspec)) (MemSbtb)).
  Proof. ss. unfold MemStb. unseal "stb". refl. Qed.

  Let client_sbtb_stb:
    (ClientStb) = (List.map (map_snd (fun ksb => (KModSem.disclose_ksb ksb): fspec)) (ClientSbtb)).
  Proof. ss. unfold ClientStb. unseal "stb". refl. Qed.

  Let _kmds: list KMod.t := [KMem; KClient].

  Lemma map_snd_map_snd A B0 B1 B2 (f0: B0 -> B1) (f1: B1 -> B2):
    (map_snd (A:=A) f1) ∘ (map_snd f0) = map_snd (f1 ∘ f0).
  Proof. apply func_ext. i. destruct x; ss. Qed.

  Let correct12: refines_closed MemClient1 MemClient2.
  Proof.
  Qed.

  Let correct23: refines_closed MemClient2 MemClient3.
  Proof.
    rp; [eapply (adequacy_open _kmds _ctxs)|..]; revgoals.
    { refl. }
    { unfold MemClient1.
      fold ctxs.
      remember _kmds. repeat f_equal. subst.
      unfold _kmds. Opaque MemSbtb. Opaque ClientSbtb. cbn.
      unfold Mem, Client.
      replace (λ ske : Sk.t,
       (map (map_snd fsb_fspec) (map (map_snd KModSem.disclose_ksb) MemSbtb) ++
        map (map_snd fsb_fspec) (map (map_snd KModSem.disclose_ksb) ClientSbtb) ++ []) ++
       flat_map
         (map (map_snd (λ _ : list val → itree (uCallE +' pE +' eventE) val, fspec_trivial2)) ∘ UModSem.fnsems)
         (map (flip UMod.get_modsem ske) _ctxs)) with
          global_stb; cycle 1.
      { apply func_ext. intro sk. rewrite app_nil_r.
        unfold global_stb.
        rewrite ! map_map. rewrite ! map_snd_map_snd.
        rewrite <- mem_sbtb_stb.
        rewrite <- client_sbtb_stb. rewrite <- List.app_assoc. repeat f_equal. }
      f_equal.
    }
  Qed.

End PROOF.
