Require Import MutHeader MutMain0 MutMain1 SimModSem Hoare.
Require Import Coqlib.
Require Import Universe.
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

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.




Ltac go := ss; igo; ired; (pfold; econs; et; i; igo; ired); try left.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Local Opaque GRA.to_URA sum.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Definition wf: W -> Prop :=
    fun w =>
      (exists mn_src mr_src,
          lookup "Main" (fst w) = Some (mn_src, mr_src)) /\
      (exists mn_tgt mr_tgt,
          lookup "Main" (snd w) = Some (mn_tgt, mr_tgt))
  .

  Theorem correct: ModSemPair.sim MutMain1.mainSem MutMain0.mainSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    2: { split; ss; et. }
    econs; ss. econs; ss. ii. subst.
    exists 100. ss. unfold mainF, mainBody, fun_to_tgt, HoareFun. ss.
    unfold forge, put, checkWf, body_to_tgt, assume, guarantee.
    inv SIMMRS. des. repeat go. des; subst.
    unfold interp_hCallE_tgt. ired. repeat rewrite interp_trigger.
    repeat go. ired. ss. rewrite Any.upcast_downcast. ss. ired.
    unfold HoareCall, forge, put, discard, checkWf, assume, guarantee.
    repeat go. eexists (_, _). left.
    repeat go. esplits; [refl|]. left. repeat go. eexists. left.
    repeat go. eexists. left. repeat go. esplits; et. left.
    repeat go. esplits; et. left. repeat go. eexists. left.
    repeat go. esplits; et. left. repeat go. esplits; et.
    { instantiate (1:=10). ss. } left. repeat go. esplits; ss. left.
    match goal with
    | [ |- paco3 _ _ _ ?i_src ?i_tgt ] => remember i_src
    end.
    rewrite <- (@bind_ret_r Es Any.t (trigger (Call "f" (Any.upcast [Vint 10])))).
    subst. pfold. econs; eauto.
    { split; esplits; ss; eauto. }
    i. inv WF. des. exists 100. left.
    repeat go. des; clarify.
    eapply f_equal with (f:=@Any.downcast val) in x7.
    repeat rewrite Any.upcast_downcast in *. clarify.
    eexists. left.
    repeat go. eexists (_, _). left.
    repeat go. esplits; [refl|]. left.
    repeat go. eexists. left. repeat go. esplits; et. left.
    repeat go. eexists. left. repeat go. esplits; et. left.
    repeat go. split; esplits; ss; eauto.
  Qed.

End SIMMODSEM.
