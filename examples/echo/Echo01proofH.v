Require Import Echo0 Echo1 HoareDef SimModSem.
Require Import Stack3A.
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
Require Import OpenDef STB.
Require Import HTactics ProofMode HSim IProofMode.

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
  Definition ClientStb: list gname.
    eapply (Seal.sealing "stb").
    let x := constr:(["getint"; "putint"]) in
    let y := eval cbn in x in
    eapply y.
  Defined.
  (* Global Opaque ClientStb. *)
  Hint Unfold ClientStb: stb.

  Variable global_stb: gname -> option fspec.
  Hypothesis STBINCL: stb_incl (to_stb_context ClientStb (EchoStb ++ StackStb)) global_stb.

  Let top2_PreOrder: @PreOrder unit top2.
  Proof. econs; eauto. Qed.
  Local Existing Instance top2_PreOrder.

  Local Opaque dec.

  Theorem sim_modsem: ModSemPair.sim (Echo1.EchoSem global_stb) (Echo0.EchoSem).
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. econs; ss.
      - eapply to_semantic. iIntros "H". ss.
    }
    econs; ss.
    { econs; ss. apply isim_fun_to_tgt_open_trivial; auto.
      unfold Echo0.echo_body, echo_body, cfunN, cfunU, ccallN, ccallU.
      iIntros. steps.
      iSplitL; auto.
      iIntros. iDes. ss. iDes. subst. steps.
      iSplitL.
      { iSplitL "INV"; auto. }
      iIntros. iDes. des; clarify.
      steps.
      iSplitL.
      { iSplitL ""; eauto. }
      iIntros. iDes. des; clarify.
      steps.
      iSplit; auto.
    }
    econs; ss.
    { econs; ss. apply isim_fun_to_tgt_open; auto.
      2:{ unfold Echo0.input_body, input_body, cfunU, ccallU, ccallN. ss.
          i. iIntros "H". iApply isim_triggerUB_src_trigger. auto. }
      unfold Echo0.input_body, input_body, cfunU, ccallU, ccallN. ss.
      iIntros. iDes. des. clarify.
      steps.
      iSplitL "INV"; auto.
      iIntros. des; clarify.
      steps.
      destruct y; ss; clarify.
      force_r; ss.
      des_ifs.
      { steps. iSplitL ""; auto. }
      steps.
      { instantiate (1:=(_, _, _)). ss. }
      { ss. }
      ss.
      iSplitR ""; auto. iIntros. iDes. subst.
      steps.
      iSplitR ""; auto.
      { iSplitL "INV"; eauto. iSplits; eauto. }
      iIntros. iDes. des; clarify.
      steps.
      iSplitL ""; auto.
    }
    econs; ss.
    { econs; ss. apply isim_fun_to_tgt_open; auto.
      2:{ unfold Echo0.input_body, input_body, cfunU, ccallU, ccallN. ss.
          i. iIntros "H". iApply isim_triggerUB_src_trigger. auto. }
      unfold Echo0.output_body, output_body, cfunU, ccallU, ccallN. ss.
      iIntros. iDes. des; clarify.
      steps.
      { instantiate (1:=(_, _)). ss. }
      { ss. }
      simpl. iSplitR ""; auto.
      iIntros. iDes. subst.
      destruct stk0; ss.
      { iDes. subst.
        steps. force_r; ss.
        des_ifs_safe. steps. iSplitL "INV"; auto.
      }
      iDes. subst.
      steps. inv H1. des; ss. force_r; ss. steps.
      des_ifs. steps.
      iSplitL "INV".
      { iSplitL "INV"; auto. }
      iIntros. subst.
      steps.
      iSplitL.
      { iSplitR; auto. }
      iIntros. iDes. des; clarify.
      steps. iSplitR; auto.
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
Hint Unfold ClientStb: stb.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk, stb_incl (to_stb_context ClientStb (EchoStb ++ StackStb)) (global_stb sk).

  Theorem correct: refines2 [Echo0.Echo] [Echo1.Echo global_stb].
  Proof.
    eapply adequacy_local2. econs; ss.
    { ii. eapply sim_modsem; ss. }
  Qed.

End SIMMOD.
