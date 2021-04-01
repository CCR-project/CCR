Require Import Mem0 Mem1 SimModSemL Hoare.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import Add0 Add1 BoxHeader.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.









Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau;
                    try rewrite interp_vis;
                    try rewrite interp_ret;
                    try rewrite interp_tau;
                    (* try rewrite interp_trigger *)
                    try rewrite interp_bind
                   ).
Ltac go := try first[pfold; econs; [..|M]; (Mskip ss); et; check_safe; ii; left|
                     pfold; econsr; [..|M]; (Mskip ss); et; check_safe; ii; left].
Ltac force_l := pfold; econs; [..|M]; Mskip ss; et.
Ltac force_r := pfold; econsr; [..|M]; Mskip ss; et.
Section SIMMODSEML.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG boxRA Σ}.

  Let W: Type := (alist mname Σ) * (alist mname Σ).

  Let wf: W -> Prop :=
    fun '(mrs_src0, mrs_tgt0) =>
      exists mr_src mr_tgt,
        (<<SRC: alist_find Dec_RelDec "Add" mrs_src0 = Some mr_src>>) /\
        (<<TGT: alist_find Dec_RelDec "Add" mrs_tgt0 = Some mr_tgt>>)
  .

  Local Opaque GRA.to_URA.
  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).

  Local Opaque AddStb BoxStb.
  Theorem correct: ModSemLPair.sim Add1.AddSem Add0.AddSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. esplits; ss; et. }
    econs; ss.
    { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify.
      unfold alist_add, alist_remove; ss.
      unfold addF.
      repeat (go; igo; ss).
      unfold assume, guarantee.
      repeat (go; igo; ss).
      des; clarify.
      rewrite ! URA.unit_idl.
      (* unfold unwrapU. des_ifs. igo. *)
      unfold addBody.
      unfold body_to_tgt. unfold interp_hCallE_tgt. igo. rewrite interp_trigger. cbn. des_ifs.
      repeat (go; igo; try rewrite interp_trigger; ss). cbn.
      des_ifs.
      Local Transparent BoxStb AddStb.
      cbn in Heq.
      Local Opaque BoxStb AddStb.
      des_ifs. cbn in *. clear_tac.
      repeat (go; igo; ss).
      rewrite URA.unit_idl in WF.
      unfold HoareCall.
      repeat (go; igo; ss).


      force_l. eexists (mr_src, client x). left.
      repeat (go; igo; ss).
      force_l. left.
      force_l. eexists. left.
      repeat (go; igo; ss).
      force_l. { rewrite URA.unit_idl; try refl. } left.
      force_l. eexists. left.
      repeat (go; igo; ss).
      unfold assume, guarantee.
      repeat (go; igo; ss).
      force_l. unshelve eexists; et. left.
      pfold; econs; et.
      { ss. esplits; et. }
      ii. exists 100%nat. left.
      repeat (go; igo; ss). des.
      repeat (go; igo; ss). des. clarify.
      repeat (go; igo; ss).
      force_l. eexists (Vint (x+1)). left.
      repeat (go; igo; ss).
      rewrite interp_trigger.
      repeat (go; igo; ss). cbn. des_ifs.
      Local Transparent BoxStb AddStb.
      cbn in Heq.
      Local Opaque BoxStb AddStb.
      des_ifs. cbn in *.
      unfold HoareCall.
      repeat (go; igo; ss).
      force_l. eexists (mr_src0, client x). left.
      repeat (go; igo; ss).
      force_l. { rewrite URA.unit_idl. eapply URA.updatable_add; try refl. } left.
      force_l. eexists (client x). left.
      repeat (go; igo; ss).
      force_l. { rewrite URA.unit_idl; ss. } left.
      force_l. exists ((x+1)%Z). left.
      repeat (go; igo; ss).
      unfold assume, guarantee.
      repeat (go; igo; ss).
      force_l. unshelve eexists; et. left.
      rewrite idK_spec with (i0:=trigger (Call "set" [Vint (x+1)])). unfold idK at 1. rewrite bind_bind.
      pfold. econs; ss; et.
      ii. des. eexists 100%nat. left.
      repeat (go; igo; ss). clarify.
      force_l. eexists (mr_src1, client (x+1)). left.
      force_l. { rewrite URA.unit_idl. eapply URA.updatable_add; try refl. } left.
      force_l. eexists (client (x+1)). left.
      repeat (go; igo; ss).
      force_l. unshelve eexists; et. left.
      force_l. { rewrite URA.unit_idl; ss. } left.
      pfold. econs; ss; et.
    }
  Qed.

End SIMMODSEML.


