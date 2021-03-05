Require Import Mem0 Mem1 SimModSem Hoare.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import BoxMain0 BoxMain1 BoxHeader.

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
Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG boxRA Σ} `{@GRA.inG (RA.excl Z) Σ}.

  Let W: Type := (alist mname Σ) * (alist mname Σ).

  Let wf: W -> Prop :=
    fun '(mrs_src0, mrs_tgt0) =>
      exists x mr_tgt,
        (<<SRC: alist_find Dec_RelDec "Main" mrs_src0 = Some (client x)>>) /\
        (<<TGT: alist_find Dec_RelDec "Main" mrs_tgt0 = Some mr_tgt>>)
  .
  (*     exists x, *)
  (*       (<<SRC: mrs_src0 = Maps.add "Box" (library x) Maps.empty>>) /\ *)
  (*       (<<TGT: mrs_tgt0 = Maps.add "Box" (GRA.embed ((inl (Some x)): URA.car (t:=RA.excl Z))) *)
  (*                                   Maps.empty>>) *)
  (* . *)

  Local Opaque GRA.to_URA.
  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).

  Local Opaque MainStb BoxStb.
  Theorem correct: ModSemPair.sim BoxMain1.MainSem BoxMain0.MainSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss; esplits; ss; et. }
    econs; ss.
    { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify.
      unfold alist_add, alist_remove; ss.
      unfold mainF.
      repeat (go; igo; ss).
      rewrite URA.unit_idl in WF.
      rename x1 into nothing. apply URA.wf_mon in WF.
      unfold assume, guarantee.
      repeat (go; igo; ss).
      rewrite ! URA.unit_idl.
      unfold body_to_tgt. unfold interp_hCallE_tgt. unfold mainBody.
      igo. rewrite interp_trigger. cbn. igo. des_ifs.
      rewrite interp_trigger. igo. cbn. des_ifs.
      Local Transparent MainStb BoxStb.
      unfold MainStb, BoxStb in Heq, Heq0.
      Local Opaque MainStb BoxStb.
      ss. des_ifs. ss.
      unfold HoareCall at 2.
      repeat (go; igo; ss).
      force_l. eexists (URA.unit, client x). left.
      repeat (go; igo; ss).
      force_l.
      { rewrite URA.unit_idl. eapply URA.extends_updatable. r. esplits; et. }
      left.
      force_l. exists (client x). left.
      repeat (go; igo; ss).
      force_l. { rewrite URA.unit_idl; ss. } left.
      force_l. exists 10%Z. left.
      unfold assume, guarantee.
      repeat (go; igo; ss).
      force_l. unshelve eexists; esplits; et. left.
      pfold. econs; ss; et.
      { esplits; et. admit "UNSOUND -- TODO". }
      i; des. esplits; et. left.




      repeat (go; igo; ss). clarify.
      rewrite URA.unit_idl in *. rewrite URA.unit_id in WF0.
      instantiate (1:=100%nat).
      unfold HoareCall.
      repeat (go; igo; ss).
      force_l. eexists (URA.unit, client 10%Z). left.
      repeat (go; igo; ss).
      force_l. { rewrite URA.unit_idl. rewrite URA.add_comm. eapply URA.extends_updatable. rr. et. } left.



      force_l. eexists (client 10%Z). left.
      repeat (go; igo; ss).
      force_l. { rewrite URA.unit_idl; ss. } left.
      force_l. exists 10%Z. left.
      unfold assume, guarantee.
      repeat (go; igo; ss).
      force_l. unshelve eexists; et. left.
      rewrite idK_spec with (i0:=trigger (Call "get" [])). unfold idK at 1. rewrite bind_bind.
      pfold. econs; et.
      { esplits; et. admit "UNSOUND -- TODO". }
      i. ss. des. eexists 100%nat. left.
      repeat (go; igo; ss).
      des. clarify.
      pfold. econs; ss; et. eexists (client x3, URA.unit). left.
      pfold. econs; ss; et.
      { rewrite URA.unit_id. rewrite URA.unit_idl. admit "ez - UNSOUND". } left.
      force_l. exists URA.unit. left.
      repeat (go; igo; ss).
      force_l. unshelve eexists; et. left.
      force_l. { rewrite URA.unit_idl; ss. } left.
      unfold idK. pfold. econs; ss; et.
    }
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.


