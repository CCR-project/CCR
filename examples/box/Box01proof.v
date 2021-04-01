Require Import Mem0 Mem1 SimModSemL Hoare.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import Box0 Box1 BoxHeader.

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
                    try rewrite interp_tau
                   (* try rewrite interp_trigger *)
                   ).
Ltac go := try first[pfold; econs; [..|M]; (Mskip ss); et; check_safe; ii; left|
                     pfold; econsr; [..|M]; (Mskip ss); et; check_safe; ii; left].
Ltac force_l := pfold; econs; [..|M]; Mskip ss; et.
Ltac force_r := pfold; econsr; [..|M]; Mskip ss; et.
Section SIMMODSEML.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG boxRA Σ} `{@GRA.inG (RA.excl Z) Σ}.

  Let W: Type := (alist mname Σ) * (alist mname Σ).

  Let wf: W -> Prop :=
    fun '(mrs_src0, mrs_tgt0) =>
      exists x,
        (<<SRC: mrs_src0 = Maps.add "Box" (library x) Maps.empty>>) /\
        (<<TGT: mrs_tgt0 = Maps.add "Box" (GRA.embed ((inl (Some x)): URA.car (t:=RA.excl Z)))
                                    Maps.empty>>)
  .

  Local Opaque GRA.to_URA.
  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).

  Theorem correct: ModSemLPair.sim Box1.BoxSem Box0.BoxSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. esplits; ss; et. }
    econs; ss.
    { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify.
      unfold alist_add, alist_remove; ss.
      unfold getF.
      repeat (go; igo; ss).
      unfold assume, guarantee.
      repeat (go; igo; ss).
      des; clarify.
      rewrite ! URA.unit_idl.
      (* unfold unwrapU. des_ifs. igo. *)
      unfold body_to_tgt. unfold interp_hCallE_tgt. rewrite interp_trigger. cbn. igo.

      assert(x = x0).
      { unfold library, client in *.
        rewrite URA.unit_idl in WF.
        rewrite GRA.embed_add in WF.
        eapply GRA.embed_wf in WF. ss. des. r in WF. des. ss. des_ifs. }
      clarify. clear WF.
      rename x0 into x.

      force_l. exists (Vint x). left.
      force_r. exists x. left.
      repeat (go; igo; ss).
      force_l. exists (library x, client x). left.
      repeat (go; igo; ss).
      force_l. exists (client x). left.
      repeat (go; igo; ss).
      force_l. unshelve esplits; ss. left.
      force_r. unshelve esplits; ss. left.
      force_l. { instantiate (1:=URA.unit). rewrite URA.unit_idl. ss. } left.
      pfold. econs; et. ss. esplits; ss; et.
    }
    econs; et.
    { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify.
      unfold alist_add, alist_remove; ss.
      unfold setF.
      repeat (go; igo; ss).
      unfold assume, guarantee.
      repeat (go; igo; ss).
      des; clarify.
      rewrite ! URA.unit_idl.
      (* unfold unwrapU. des_ifs. igo. *)
      unfold body_to_tgt. unfold interp_hCallE_tgt. rewrite interp_trigger. cbn. igo.

      (* assert(x = x0). *)
      (* { unfold library, client in *. *)
      (*   rewrite URA.unit_idl in WF. *)
      (*   rewrite GRA.embed_add in WF. *)
      (*   eapply GRA.embed_wf in WF. ss. des. r in WF. des. ss. des_ifs. } *)
      (* clarify. clear WF. *)
      (* rename x0 into x. *)

      rename x0 into x_new.
      force_l. exists (Vint 0). left.
      repeat (go; igo; ss).
      force_l. exists (library x_new, client x_new). left.
      force_l.
      { unfold library, client.
        rewrite ! GRA.embed_add. eapply GRA.embed_updatable. ss.
        rr. ii. des_ifs. ss. des_ifs; des; ss.
        - rr in H1. des; clarify. ss. des_ifs.
        - rr in H1. des; clarify. ss. des_ifs.
          esplits; ss; et. rr. exists (inr tt). ss.
      }
      left.
      repeat (go; igo; ss).
      force_l. exists (client x_new). left.
      repeat (go; igo; ss).
      force_l. unshelve esplits; ss. left.
      force_l. { instantiate (1:=URA.unit). rewrite URA.unit_idl. ss. } left.
      unfold MPut.
      repeat (go; igo; ss).
      pfold. econs; ss; et. esplits; ss; et.
    }
  Qed.

End SIMMODSEML.


