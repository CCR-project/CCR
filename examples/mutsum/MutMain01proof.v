Require Import HoareDef MutHeader MutMain0 MutMain1 SimModSem.
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



(* TODO: move to SimModSem & add cpn3_wcompat *)
Hint Resolve sim_itree_mon: paco.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Local Opaque GRA.to_URA sum.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = Maps.add "Main" (ε, tt↑) Maps.empty>>) /\
      (<<TGT: mrps_tgt0 = Maps.add "Main" (ε, tt↑) Maps.empty>>)
  .

  Theorem correct: ModSemPair.sim MutMain1.mainSem MutMain0.mainSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss. init.
    unfold mainF, checkWf, forge, discard, put. steps. des; subst.
    unfold APC. unfold body_to_tgt, mainBody, interp_hCallE_tgt. steps.
    rewrite Any.upcast_downcast in *. ss. steps.
    unfold HoareCall, checkWf, forge, discard, put. steps.
    force_l. eexists (_, _). steps. force_l.
    { refl. }
    steps. force_l. eexists. steps. force_l. eexists. force_l.
    { refl. }
    steps. force_l. exists 10. force_l. eexists. force_l. eexists. force_l.
    { esplits; et. }
    force_l.
    { splits; ss. } ired.
    match goal with
    | [ |- gpaco3 _ _ _ _ _ ?i_src ?i_tgt ] => remember i_src
    end.
    rewrite <- (@bind_ret_r Es Any.t (trigger (Call "f" (Any.upcast [Vint 10])))).
    subst. gstep. econs; ss. i. des; clarify. unfold alist_add. ss. exists 100.
    steps. des; clarify. force_l. eexists. force_l. eexists (_, _). steps. force_l.
    { refl. }
    steps. force_l. eexists. force_l.
    { splits; ss. }
    steps. force_l. eexists. force_l; ss. steps.
  Qed.

End SIMMODSEM.
