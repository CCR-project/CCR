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
Require Import Logic TODOYJ.





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


Section AUX.
  (* TODO: move to AList.v *)
  Lemma map_snd_map_snd A B0 B1 B2 (f0: B0 -> B1) (f1: B1 -> B2):
    (map_snd (A:=A) f1) ∘ (map_snd f0) = map_snd (f1 ∘ f0).
  Proof. apply func_ext. i. destruct x; ss. Qed.

  Lemma find_alist_find
        `{Dec K} V (k: K) (kvs: list (K * V))
    :
      alist_find k kvs = o_map (find (fun '(k0, _) => dec k k0) kvs) snd
  .
  Proof.
    ginduction kvs; ii; ss. des_ifs; rewrite eq_rel_dec_correct in *; des_sumbool; des_ifs.
  Qed.

  Lemma alist_find_app2 K `{Dec K} V (k: K) (l0 l1: alist K V) (v: V)
        (FIND0: alist_find k l0 = None)
        (FIND1: alist_find k l1 = Some v)
    :
      alist_find k (l0 ++ l1) = Some v.
  Proof.
    ginduction l0; ii; ss. des_ifs; try rewrite eq_rel_dec_correct in *; des_sumbool; des_ifs.
    eapply IHl0; et.
  Qed.

  Lemma alist_find_flat_map
        `{Dec K} V0 V1 (k: K) (f: V0 -> alist K V1) (l: list V0)

        kvs v
        (FIND0: find (is_some ∘ alist_find k) (map f l) = Some kvs)
        (FIND1: alist_find k kvs = Some v)
    :
      alist_find k (flat_map f l) = Some v
  .
  Proof.
    ginduction l; ii; ss. des_ifs; try rewrite eq_rel_dec_correct in *; des_sumbool; des_ifs.
    - erewrite alist_find_app; et.
    - erewrite alist_find_app2; et. unfold is_some in Heq. des_ifs.
  Qed.

  Lemma in_alist_find
        `{Dec K} V kv kvs
        (IN: In kv kvs)
    :
      exists (v: V), alist_find (fst kv) kvs = Some v
  .
  Proof.
    ginduction kvs; ii; ss. des; subst.
    - des_ifs; try rewrite eq_rel_dec_correct in *; des_sumbool; des_ifs; et.
    - des_ifs; try rewrite eq_rel_dec_correct in *; des_sumbool; des_ifs; et.
  Qed.

  Lemma alist_find_flat_map_const
        `{Dec K} V0 V1 V2 (k: K) (f: V0 -> alist K V1) (l: list V0)

        (c: V2)
        (IN: In k (concat (map (map fst ∘ f) l)))
        (* (FIND0: find (is_some ∘ alist_find k) (map f l) = Some kvs) *)
    :
      alist_find k (flat_map (map (map_snd (fun _ => c)) ∘ f) l) = Some c
  .
  Proof.
    ginduction l; ii; ss.
    rewrite in_app_iff in *; des.
    - rewrite in_map_iff in *. des; subst.
      erewrite alist_find_app; et. unfold map_snd. erewrite alist_find_map.
      exploit in_alist_find; et. intro T; des. rewrite T. ss.
    - destruct (alist_find k (map (map_snd (λ _ : V1, c)) (f a))) eqn:T.
      + erewrite alist_find_app; et. unfold map_snd. erewrite alist_find_map.
        dup T. eapply alist_find_some in T0. rewrite in_map_iff in *. des; subst. destruct x; ss; clarify.
        eapply in_alist_find in T1. des. ss. rewrite T1. ss.
      + erewrite alist_find_app2; et.
  Qed.

End AUX.



Section WEAKENING.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.


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

  Hypothesis HASNAME:
    forall sk, In "unknown_call"
                  (concat (map (map fst ∘ UModSem.fnsems) (map (flip UMod.get_modsem sk) _ctxs))).

  Let correct12: refines_closed MemClient1 MemClient2.
  Proof.
    eapply refines_close.
    unfold MemClient1, MemClient2.
    rewrite ! Mod.add_list_app.
    eapply (SimModSem.refines_proper_r).
    apply adequacy_local_list.
    econs.
    { eapply adequacy_weaken. ii. ss. }
    econs.
    { eapply adequacy_weaken. ii. ss. unfold global_stb. stb_tac.
      autounfold with stb; autorewrite with stb; simpl. (*** TODO: FIX STB TAC ***)
      des_ifs.
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs; try (by esplits; et; refl).
      - rewrite eq_rel_dec_correct in *; des_ifs.
        erewrite alist_find_flat_map_const.
        { esplits; et. refl. }
        et.
    }
    econs.
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

  Theorem correct: refines_closed MemClient0 MemClient3.
  Proof.
    etrans; [eapply correct01|].
    etrans; [eapply correct12|].
    etrans; [eapply correct23|].
    refl.
  Qed.

End PROOF.
