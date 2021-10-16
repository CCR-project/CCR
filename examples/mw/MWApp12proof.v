Require Import HoareDef MWHeader MWApp1 MWApp2 SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import HTactics ProofMode.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG AppRA Σ}.
  Context `{@GRA.inG mwRA Σ}.

  Let W: Type := Any.t * Any.t.

  (* Let wf: _ -> W -> Prop := fun (_: unit) '(mr_src, mr_tgt) => mr_src = mr_tgt. *)
  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (* (fun _ _ mpr_tgt => (∃ (mr_tgt: AppRA), ⌜mpr_tgt = Any.pair tt↑ (GRA.embed mr_tgt)↑⌝ ** OwnM mr_tgt)%I) *)
      (fun _ _ mpr_tgt mr_src => mpr_tgt = Any.pair tt↑ mr_src↑)
  .

  (* Variant mk_wf (A: Type) *)
  (*         (R: A -> Any.t -> Any.t -> iProp) *)
  (*   : A -> Any.t * Any.t -> Prop := *)
  (* | mk_wf_intro *)
  (*     a *)
  (*     mr_src mp_src mp_tgt *)
  (*     (RSRC: URA.wf mr_src -> R a mp_src mp_tgt mr_src) *)
  (*   : *)
  (*     mk_wf R a ((Any.pair mp_src mr_src↑), mp_tgt) *)
  (* . *)





  (* Lemma iPropL_reclaim (Hn: string) (l: iPropL) P *)
  (*       (FIND: alist_find Hn l = Some P) *)
  (*   : *)
  (*     from_iPropL l -∗ #=> ∃ rP, from_iPropL (alist_remove Hn l). *)
  (* Proof. *)
  (*   induction l; ss. *)
  (*   { iIntros "H". iModIntro. iFrame. } *)
  (*   { destruct a. iIntros "[H0 H1]". rewrite eq_rel_dec_correct. des_ifs; ss. *)
  (*     { iPoseProof (IHl with "H1") as "> H1". *)
  (*       iModIntro. iFrame. } *)
  (*     { iPoseProof (IHl with "H1") as "> H1". *)
  (*       iClear "H0". iModIntro. iFrame. } *)
  (*   } *)
  (* Qed. *)

  Lemma current_iPropL_reclaim
        ctx hd tl
        (P: current_iPropL ctx (hd :: tl))
    :
      exists hdr, <<TL: current_iPropL (ctx ⋅ hdr) tl>> ∧ <<HD: hd.2 hdr>>
  .
  Proof.
    rr in P. inv P. destruct hd. ss. unfold from_iPropL in IPROP. fold from_iPropL in IPROP.
    rr in IPROP. rewrite Seal.sealing_eq in *. des. subst. esplits; et.
    rr. econs; et. rewrite URA.add_assoc. rewrite URA.add_comm. rewrite URA.add_assoc. ss.
  Qed.

  (* Lemma current_iPropL_reclaim *)
  (*       l ctx Hn P *)
  (*       (I: current_iPropL ctx l) *)
  (*       (FIND: alist_find Hn l = Some P) *)
  (*   : *)
  (*     exists rP, <<TL: current_iPropL (ctx ⋅ rP) (alist_remove Hn l)>> ∧ <<HD: P rP>> *)
  (* . *)
  (* Proof. *)
  (*   unfold current_iPropL in *. *)
  (*   revert_until l. induction l; ii; ss. des_ifs_safe. ss. des_ifs. *)
  (*   - unfold from_iPropL in I. fold from_iPropL in I. inv I. ss. *)
  (*     rr in IPROP. rewrite Seal.sealing_eq in *. des. subst. *)
  (*     exploit IHl; et. *)
  (*     { econs; [|et]. instantiate (1:=a ⋅ ctx). rewrite URA.add_comm. rewrite <- URA.add_assoc. *)
  (*       erewrite URA.add_comm with (a0:=ctx). rewrite URA.add_assoc. ss. } *)
  (*     i; des. esplits; et. *)
  (*     inv TL. econs; et. *)
  (*     { instantiate (1:=r ⋅ a). erewrite f_equal; et. rewrite ! URA.add_assoc. ss. } *)
  (*     unfold from_iPropL. fold from_iPropL. *)
  (*     rr. rewrite Seal.sealing_eq. esplits; revgoals; et. rewrite URA.add_comm. ss. *)
  (*   - unfold from_iPropL in I. fold from_iPropL in I. inv I. ss. *)
  (*     rr in IPROP. rewrite Seal.sealing_eq in *. des. subst. *)

  (*     esplits; et. *)
  (*     { econs. *)

  (*     exploit IHl; et. *)
  (*     { econs; [|et]. instantiate (1:=a ⋅ ctx). rewrite URA.add_comm. rewrite <- URA.add_assoc. *)
  (*       erewrite URA.add_comm with (a0:=ctx). rewrite URA.add_assoc. ss. } *)
  (*     i; des. esplits; et. *)
  (*     inv TL. econs; et. *)
  (*     { instantiate (1:=r ⋅ a). erewrite f_equal; et. rewrite ! URA.add_assoc. ss. } *)
  (*     unfold from_iPropL. fold from_iPropL. *)
  (*     rr. rewrite Seal.sealing_eq. esplits; revgoals; et. rewrite URA.add_comm. ss. *)
  (*   - ss. *)
  (*     ss. *)
  (*   rr in I. inv I. destruct hd. ss. unfold from_iPropL in IPROP. fold from_iPropL in IPROP. *)
  (*   rr in IPROP. rewrite Seal.sealing_eq in *. des. subst. esplits; et. *)
  (*   rr. econs; et. rewrite URA.add_assoc. rewrite URA.add_comm. rewrite URA.add_assoc. ss. *)
  (* Qed. *)

  Theorem correct: refines2 [MWApp1.App] [MWApp2.App].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { ss. }
    (* { esplits. econs; ss. eapply to_semantic. iIntros "H". iSplits; ss. } *)
    { esplits. econs; ss. }

    econs; ss.
    { init. harg. mDesAll. des; clarify. rename x into mwf.
      mAssert _ with "INV" as "I".
      { iExact "INV". }
      apply current_iPropL_reclaim in ACC. des. ss. subst.

      (*** AppInit is reasoned from the lower layer ***)

      rewrite HoareFun_parse.
      Local Transparent HoareFunArg. unfold HoareFunArg. Local Opaque HoareFunArg.
      steps. force_r. esplits; et. steps.
      force_r. exists (([]: list val)↑). steps. force_r.
      exists (GRA.embed AppInit, ctx ⋅ (GRA.embed (A:=mwRA) mwf)). steps.
      unfold mget. steps.
      force_r.
      { admit "ez". }
      steps. force_r. exists ord_top. steps. force_r.
      { eapply to_semantic; et. admit "ez". }
      steps. unfold ccallU at 2. steps.

      Local Transparent HoareCall. unfold HoareCall. Local Opaque HoareCall.
      steps. unfold mput. steps. ss.
      rr in _GUARANTEE0. clear _ASSUME0.
      uipropall. des; clarify. clear_tac.
      unfold ccallU. steps.
      replace (ctx ⋅ hdr) with ctx in TL by admit "ez".
      hcall _ (_, _, _) _ with "*".
      { iModIntro. iFrame. iSplits; ss; et.
      }

      Local Transparent HoareFunRet. unfold HoareFunRet. Local Opaque HoareFunRet.

      unfold HoareFunRet.



      unfold initF, ccallU. steps.
      mDesOr "INV"; mDesAll; des; clarify.
      2: { mAssertPure False; ss. iCombine "INV A" as "A". iOwnWf "A" as WF0. admit "ez". }
      steps. rewrite Any.upcast_downcast in *. clarify. steps.
      hcall _ _ _ with "INV"; auto.
      { esplits; ss. }
      steps. mDesAll; clarify. mDesOr "INV1"; mDesAll; clarify.
      2: { mAssertPure False; ss. iCombine "INV1 A" as "A". iOwnWf "A" as WF0. admit "ez". }
      rewrite _UNWRAPU. steps.
      mAssert _ with "*".
      { iCombine "A" "INV1" as "A". iApply (OwnM_Upd with "A").
        instantiate (1:=AppRun ⋅ AppRunX). admit "ez". }
      hret _; ss.
      { iMod "A1". iDestruct "A1" as "[A B]". iFrame. iSplits; ss; et. }
    }
    econs; ss.
    { init. harg. mDesAll. des; clarify. unfold runF, ccallU. steps.
      mDesOr "INV"; mDesAll; des; clarify.
      1: { mAssertPure False; ss. iCombine "INV A" as "A". iOwnWf "A" as WF0. admit "ez". }
      steps. rewrite Any.upcast_downcast in *. clarify. steps.
      hcall _ _ _ with "INV"; auto.
      { esplits; ss. }
      steps. mDesAll; clarify. mDesOr "INV1"; mDesAll; clarify.
      1: { mAssertPure False; ss. iCombine "INV1 A" as "A". iOwnWf "A" as WF0. admit "ez". }
      rewrite _UNWRAPU. steps.
      hret _; ss.
      { iFrame. iSplits; ss; et. }
    }
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
