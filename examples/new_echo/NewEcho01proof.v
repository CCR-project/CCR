Require Import NewEcho0 NewEcho1 HoareDef SimModSem.
Require Import NewStack3A.
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
Require Import TODOYJ.
Require Import HTactics Logic IPM.
Require Import OpenDef STB.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf _ unit
           (fun _ _ _ => ⌜True⌝%I)
  .

  (*** TODO: remove this later ***)
  Definition ClientStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (fun fn => (fn, fspec_trivial)) ["getint"; "putint"]) in
    let y := eval cbn in x in
    eapply y.
  Defined.
  (* Global Opaque ClientStb. *)
  Hint Unfold ClientStb: stb.

  Variable global_stb: gname -> option fspec.
  Hypothesis STBINCL: stb_incl (to_stb (ClientStb ++ EchoStb ++ StackStb)) global_stb.

  Ltac renamer := idtac.
  Ltac post_call :=
    fold wf; clear_fast; mDesAll; des_safe; subst; try rewrite Any.upcast_downcast in *; clarify; renamer.

  (* Local Opaque is_int_stack. *)
  (* Lemma unfold_is_int_stack *)
  (*       h stk0 *)
  (*   : *)
  (*     is_int_stack h stk0 = is_int_stack h stk0 *)
  (* . *)
  (* Proof. *)
  (* Qed. *)

  Theorem sim_modsem: ModSemPair.sim (NewEcho1.EchoSem global_stb) (NewEcho0.EchoSem).
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. econs; ss.
      - eapply to_semantic. iIntros "H". ss.
    }
    econs; ss.
    { unfold NewEcho0.echo_body, echo_body, cfunN, cfunU, ccallN, ccallU.
      kinit. harg. post_call.
      des_ifs. steps.
      astart 1. acatch. { eapply STBINCL. stb_tac; ss. } hcall _ _ _ with ""; ss; et.
      post_call. steps. astop. steps. erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ _ with "A"; ss; et.
      { iModIntro. iSplits; ss; et. }
      { ss. }
      post_call. steps.
      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ _ with "A"; ss; et.
      { iModIntro. iSplits; ss; et. }
      { ss. }
      post_call. steps.
      hret _; ss.
    }
    econs; ss.
    { unfold NewEcho0.input_body, input_body, cfunU, ccallU, ccallN. kinit.
      2: { harg. mDesAll. des; clarify. steps. }
      harg. post_call. steps.
      erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
      hcall _ _ _ with ""; ss; et.
      post_call. steps.
      hide_k. force_r.
      { unshelve esplits; et. }
      unhide_k.
      hide_k. steps. unhide_k.
      ss. clarify.
      des_ifs.
      - steps. hret _; ss.
        { iModIntro. iSplits; ss; et. }
      - steps.
        astart 1. acatch.
        { erewrite STBINCL; ss. stb_tac; ss. }
        hcall _ (_, _, _) _ with "-"; ss; et.
        { ss. }
        post_call. steps. astop. steps.

        erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
        hcall _ _ _ with "-"; ss; et.
        { iModIntro. iSplits; ss; et. }
        { ss. }
        post_call. steps.
        hret _; ss.
        { iModIntro. iSplits; ss; et. }
    }
    econs; ss.
    { unfold NewEcho0.output_body, output_body, cfunU, ccallU, ccallN. kinit.
      2:{ harg. mDesAll. des; clarify. steps. }
      harg. post_call. steps.
      astart 1. acatch.
      { erewrite STBINCL; ss. stb_tac; ss. }
      hcall _ (_, _) _ with "-"; ss; et.
      { ss. }
      post_call. steps. astop. steps.
      destruct a as [|hd tl]; ss.
      - steps. mDesAll; ss; des; subst. rewrite Any.upcast_downcast in *. clarify. steps.
        force_r; ss. grind.
        hret _; ss.
        { iModIntro. iSplits; ss; et. }
      - steps. mDesAll; ss; des; subst. rewrite Any.upcast_downcast in *. clarify.
        erewrite STBINCL; cycle 1.
        { stb_tac; ss. }
        Local Opaque dec. steps. Local Transparent dec.
        inv PURE. des.
        hide_k.
        force_r; ss. grind.
        unhide_k.
        des_ifs. steps.
        hcall _ _ _ with ""; ss; et.
        post_call. steps.
        erewrite STBINCL; cycle 1. { stb_tac; ss. } steps.
        hcall _ _ _ with "-"; ss; et.
        { iModIntro. iSplits; ss; et. }
        { ss. }
        post_call. steps.
        hret _; ss.
        { iModIntro. iSplits; ss; et. }
    }
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk, stb_incl (to_stb (ClientStb ++ EchoStb ++ StackStb)) (global_stb sk).

  Theorem correct: ModPair.sim (NewEcho1.Echo global_stb) (NewEcho0.Echo).
  Proof.
    econs; ss.
    { ii. eapply sim_modsem; ss. }
  Qed.

End SIMMOD.
