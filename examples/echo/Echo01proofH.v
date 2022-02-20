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

  Theorem sim_modsem: ModSemPair.sim (Echo1.EchoSem global_stb) (Echo0.EchoSem).
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. econs; ss.
      - eapply to_semantic. iIntros "H". ss.
    }
    econs; ss.
    { econs; ss. apply isim_fun_to_tgt_open_trivial; auto.
      unfold Echo0.echo_body, echo_body, cfunN, cfunU, ccallN, ccallU.
      i. iIntros "INV".
      iApply isim_unwrapU_src. iIntros (l) "EQ".
      iApply isim_unwrapU_tgt. iExists l. iSplit; [iApply "EQ"|].
      destruct l; ss.
      2:{ hred_l. iApply isim_triggerUB_src. auto. }
      hred_l. hred_r. iApply isim_apc. iExists (Some (1: Ord.t)). hred_l.
      iApply isim_call_pure.
      { eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss]. }
      { oauto. }
      iSplitL "INV"; auto.
      simpl. iIntros (st_src0 st_tgt0 ret_src ret_tgt) "[INV POST]".
      iDestruct "POST" as "[POST %]". iDestruct "POST" as (n) "[% OWN]".
      subst. hred_r.
      iApply isim_call_impure.
      { eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss]. }
      simpl. iSplitL "INV OWN".
      { iSplitL "INV"; auto. }
      iIntros (st_src1 st_tgt1 ret_src ret_tgt) "INV POST".
      iDestruct "POST" as (stk1) "[% [OWN %]]".
      des; clarify. hred_l. hred_r.
      iApply isim_apc. iExists None. hred_l.
      iApply isim_call_impure.
      { eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss]. }
      simpl. iSplitL "INV OWN".
      { iSplitL "INV"; auto. }
      iIntros (st_src2 st_tgt2 ret_src ret_tgt) "INV POST".
      iDestruct "POST" as (stk2) "[% [OWN %]]".
      des; clarify. hred_l. hred_r.
      iApply isim_apc. iExists None. hred_l.
      iApply isim_ret. iSplit; auto.
    }
    econs; ss.
    { econs; ss. apply isim_fun_to_tgt_open; auto.
      2:{ unfold Echo0.input_body, input_body, cfunU, ccallU, ccallN. ss.
          i. iIntros "H". iApply isim_triggerUB_src_trigger. auto. }
      unfold Echo0.input_body, input_body, cfunU, ccallU, ccallN. ss.
      i. iIntros "[INV POST]".
      iDestruct "POST" as (? ?) "[% [POST %]]". des; clarify.
      hred_l. hred_r.
      iApply isim_call_impure.
      { eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss]. }
      simpl. iSplitL "INV"; auto.
      iIntros (? ? ? ?) "INV %". subst. hred_l. hred_r.
      iApply isim_unwrapU_src. iIntros (v) "%".
      iApply isim_unwrapU_tgt. iExists v. iSplit; auto.
      hred_l. hred_r. iApply isim_apc. iExists None.
      hred_l. iApply isim_assume_src. iIntros "%".
      hred_l. iApply isim_unwrapU_src. iIntros (n) "%".
      destruct v; ss; clarify.
      iApply isim_assume_tgt. iSplit; auto. des_ifs.
      { hred_l. iApply isim_apc. iExists None.
        hred_l. hred_r. iApply isim_ret. iSplitL "INV"; auto. }
      { hred_l. iApply isim_apc. iExists (Some (1: Ord.t)).
        hred_l. hred_r. iApply isim_call_pure.
      { eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss].
        { instantiate (1:=(_, _, _)). ss. }
        { ss. }
      }
      { oauto. }
      simpl. iSplitR ""; auto. iIntros (? ? ? ?) "[INV [[OWN %] %]]".
      subst. hred_r. iApply isim_call_impure.
      { eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss]. }
      simpl. iSplitR ""; auto.
      { iSplitL "INV"; eauto. iExists _. iExists _. iSplit; auto. }
      iIntros (? ? ? ?) "INV POST". hred_l. hred_r.
      iDestruct "POST" as (stk1) "[% [OWN %]]". des; clarify.
      hred_l. hred_r. iApply isim_apc. iExists None. hred_l.
      iApply isim_ret. iSplitL "INV"; auto.
      }
    }
    econs; ss.
    { econs; ss. apply isim_fun_to_tgt_open; auto.
      2:{ unfold Echo0.input_body, input_body, cfunU, ccallU, ccallN. ss.
          i. iIntros "H". iApply isim_triggerUB_src_trigger. auto. }
      unfold Echo0.output_body, output_body, cfunU, ccallU, ccallN. ss.
      i. iIntros "[INV POST]".
      iDestruct "POST" as (? ?) "[% [POST %]]". des; clarify.
      hred_l. hred_r. iApply isim_apc. iExists (Some (1: Ord.t)).
      iApply isim_call_pure.
      { eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss].
        { instantiate (1:=(_, _)). ss. }
        { ss. }
      }
      { oauto. }
      simpl. iSplitR ""; auto.
      iIntros (? ? ? ?) "[INV [POST %]]". subst.
      destruct stk0; ss.
      { iDestruct "POST" as "[% OWN]". subst.
        hred_r. iApply isim_assume_tgt. iSplit; auto.
        hred_l. hred_r. iApply isim_ret. iSplitL "INV"; auto.
      }
      iDestruct "POST" as "[% OWN]". subst.
      Local Opaque dec. hred_r.
      iApply isim_assume_tgt. inv H1. des. iSplit; auto.
      hred_l. des_ifs. hred_r.
      iApply isim_call_impure.
      { eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss]. }
      simpl. iSplitL "INV".
      { iSplitL "INV"; auto. }
      iIntros (st_src1 st_tgt1 ret_src ret_tgt) "INV %". subst.
      hred_l. iApply isim_unwrapU_src. iIntros (v) "%".
      hred_r. iApply isim_unwrapU_tgt. iExists v. iSplit; auto.
      hred_l. iApply isim_apc. iExists None. hred_l. hred_r.
      iApply isim_call_impure.
      { eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss]. }
      simpl. iSplitL "INV OWN".
      { iSplitL "INV"; auto. }
      iIntros (? ? ? ?) "INV POST".
      iDestruct "POST" as (stk1) "[% [OWN %]]". des; clarify.
      hred_l. hred_r. iApply isim_apc. iExists None.
      hred_l. iApply isim_ret. iSplitL "INV"; auto.
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
