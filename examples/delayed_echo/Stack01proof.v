Require Import Mem1.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef Stack0 Stack1 SimModSem.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import HTactics TODOYJ YPM.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section AUX.
  Context `{Σ: GRA.t}.

  Lemma _Own_ε: Own ε = ⌜True⌝. Proof. apply func_ext; i. unfold Own. apply prop_ext. split; i; ss. r. esplit. rewrite URA.unit_idl; refl. Qed.
  Lemma Own_ε: ⌞Own ε⌟. Proof. iIntro. rewrite _Own_ε. ss. Fail Qed. Abort. (********** coq bug !!!!!!!!!!!!!!! **************)
  Lemma Own_ε: ⌞Own ε⌟. Proof. iIntro. exists r. r_solve. Qed.

  Lemma iHyp_update_r: forall P r0 r1, r0 = r1 -> iHyp P r0 -> iHyp P r1. Proof. i. subst. ss. Qed.
  Lemma unit_id': forall r0 (my_ε: Σ), my_ε = ε -> r0 ⋅ my_ε = r0. Proof. i. subst. r_solve. Qed.

End AUX.
Global Opaque _APC.

Ltac iImpure H :=
  let name := fresh "my_r" in
  specialize (H ε URA.wf_unit I); rewrite intro_iHyp in H;
  (* set (name:=ε); *) (*** <- it has side effect in goal ***)
  pose (name:=(@URA.unit (GRA.to_URA _)));
  eapply iHyp_update_r with (r1:=name) in H; [|refl];
  on_gwf ltac:(fun GWF => erewrite <- unit_id' with (my_ε:=name) in GWF; [|refl]);
  match goal with
  | [ |- (gpaco3 (SimModSem._sim_itree _) _ _ _ _ _  _) ] => idtac
  | [ |- iHyp _ _ ] => erewrite <- unit_id' with (my_ε:=name); [|refl]
  | _ => idtac
  end;
  clearbody name
.





Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  Eval compute in (@URA.car Mem1._memRA).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
        (<<SRC: mrps_src0 = Maps.add "Stack" (ε, tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "Stack" (ε, tt↑) Maps.empty>>)
  .

  Local Opaque points_to.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.

  Theorem correct: ModSemPair.sim Stack1.StackSem Stack0.StackSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. }

    econs; ss.
    { unfold popF. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      iRefresh. do 4 iDestruct PRE. iMod A. iMod PRE. clarify.
      apply Any.upcast_inj in PRE. des; clarify. steps. rewrite Any.upcast_downcast in *. clarify. steps.

      unfold ccall. steps. astart 10.

      acall_tac __ __ (@URA.unit Σ) A0 A1; ss; et.
      { instantiate (2:= (_, _, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss; et. }
      { esplits; ss; et. eauto with ord_step. }
      des; subst. rewrite Any.upcast_downcast. steps. iRefresh. iDestruct POST. iMod A. apply Any.upcast_inj in A; des; clarify.


      destruct l; ss.
      - iMod A0. subst.
        hexploit Own_ε; intro A. iImpure A.
        acall_tac __ __ (@URA.unit Σ) POST A; ss; et.
        { instantiate (2:= (_, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitR A; ss; et. right; iRefresh. rr. esplits; et. }
        { esplits; ss. eauto with ord_step. }
        des; subst. rewrite Any.upcast_downcast. steps. iRefresh. iDestruct POST0. iMod A. apply Any.upcast_inj in A; des; clarify.
        clear POST0. steps.

        astop. force_l. eexists. hret_tac (@URA.unit Σ) POST; ss.
      - do 4 iDestruct A0. iMod A0. subst.
        rename n into rref. rename x6 into hd. rename x7 into next.
        rewrite points_to_split in A1. rewrite <- GRA.embed_add in A1. rewrite own_sep in A1. iDestruct A1. ss.
        acall_tac __ __ (@URA.unit Σ) (A, A0, POST) A1; ss; et.
        { instantiate (2:= (_, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitR A1; ss; et. do 4 left; do 3 eexists; iRefresh.
          iSplitP; ss. iSplitP; ss. }
        { esplits; ss. eauto with ord_step. }
        des; subst. rewrite Any.upcast_downcast. steps. iRefresh. iDestruct POST0. iMod A1. apply Any.upcast_inj in A1; des; clarify.
        steps.

        acall_tac __ __ (@URA.unit Σ) (A0, A, POST) POST0; ss; et.
        { instantiate (2:=(_, _, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. iDestruct POST1. iMod A1. apply Any.upcast_inj in A1. des; clarify. steps.


        acall_tac __ __ (@URA.unit Σ) (A, POST, POST1) A0; ss; et.
        { instantiate (2:=(_, _, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. iDestruct POST0. iMod A0. apply Any.upcast_inj in A0. des; clarify. steps.
        rewrite Any.upcast_downcast in *. clarify.


        acall_tac __ __ (@URA.unit Σ) (A, POST, POST0) POST1; ss; et.
        { instantiate (2:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. subst. steps. rewrite Any.upcast_downcast in *. clarify.


        acall_tac __ __ (@URA.unit Σ) (A, POST) POST0; ss; et.
        { instantiate (2:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. subst. steps. rewrite Any.upcast_downcast in *. clarify.


        acall_tac __ __ (@URA.unit Σ) (A) POST; ss; et.
        { instantiate (2:=(_, _, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. subst. steps. rewrite Any.upcast_downcast in *. clarify.

        astop. force_l. eexists.
        hret_tac (@URA.unit Σ) (POST0, A); ss.
        { esplits; try refl; iRefresh. iSplitP; ss. eexists; iRefresh. iSplitR A; et. }
    }
    econs; ss.
    { unfold pop2F. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      iRefresh. do 4 iDestruct PRE. iDestruct A0. iMod A. iMod PRE. clarify.
      apply Any.upcast_inj in PRE. des; clarify. steps. rewrite Any.upcast_downcast in *. clarify. steps.

      unfold ccall. astart 10. steps.

      destruct l; ss.
      - iMod A1; subst.
        hexploit Own_ε; intro A. iImpure A.
        acall_tac __ __ (@URA.unit Σ) A0 A; ss; et.
        { instantiate (2:= (_, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitR A; ss; et. right; iRefresh. rr. esplits; et. }
        { esplits; ss. eauto with ord_step. }
        des; subst. rewrite Any.upcast_downcast. steps. iRefresh. iDestruct POST. iMod A. apply Any.upcast_inj in A; des; clarify.
        clear POST. steps.

        astop. force_l. eexists.
        hret_tac (@URA.unit Σ) A0; ss.
      - do 4 iDestruct A1. iMod A1. subst.
        rename n into iref. rename x2 into unknown. rename x5 into hd. rename x6 into next. rename A2 into A1.

        rewrite points_to_split in A1. rewrite <- GRA.embed_add in A1. rewrite own_sep in A1. iDestruct A1. ss.
        acall_tac __ __ (@URA.unit Σ) (A, A0, A2) A1; ss; et.
        { instantiate (2:= (_, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitR A1; ss; et. do 4 left; do 3 eexists; iRefresh.
          iSplitP; ss. iSplitP; ss. }
        { esplits; ss. eauto with ord_step. }
        des; subst. rewrite Any.upcast_downcast. steps. iRefresh. iDestruct POST. iMod A1. apply Any.upcast_inj in A1; des; clarify.
        steps.

        acall_tac __ __ (@URA.unit Σ) (A0, A, A2) POST; ss; et.
        { instantiate (2:=(_, _, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. iDestruct POST0. iMod A1. apply Any.upcast_inj in A1. des; clarify. steps.


        acall_tac __ __ (@URA.unit Σ) (A, A0, POST0) A2; ss; et.
        { instantiate (2:=(_, _, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. iDestruct POST. iMod A1. apply Any.upcast_inj in A1. des; clarify. steps.
        rewrite Any.upcast_downcast in *. clarify.


        acall_tac __ __ (@URA.unit Σ) (A, A0, POST) POST0; ss; et.
        { instantiate (2:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. subst. steps. rewrite Any.upcast_downcast in *. clarify.


        acall_tac __ __ (@URA.unit Σ) (A, A0) POST; ss; et.
        { instantiate (2:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. subst. steps. rewrite Any.upcast_downcast in *. clarify.


        acall_tac __ __ (@URA.unit Σ) (A) A0; ss; et.
        { instantiate (2:=(_, _, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. subst. steps. rewrite Any.upcast_downcast in *. clarify.

        astop. force_l. eexists.
        hret_tac (@URA.unit Σ) (POST, A); ss.
        { esplits; try refl; iRefresh. eexists; iRefresh. iSplitR POST; ss. iSplitP; ss. }
    }
    econs; ss.
    { unfold pushF. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      iRefresh. do 3 iDestruct PRE. iMod A. iMod PRE. clarify.
      apply Any.upcast_inj in PRE. des; clarify. steps. rewrite Any.upcast_downcast in *. clarify. steps.

      unfold ccall. astart 10. steps.

      acall_tac __ __ (@URA.unit Σ) A0 (@URA.unit Σ); ss; et.
      { instantiate (2:=2). esplits; try refl; iRefresh. ss. }
      { esplits; ss. eauto with ord_step. }
      des; iRefresh. subst. do 2 iDestruct POST. iMod POST. rewrite Any.upcast_downcast. apply Any.upcast_inj in POST. des; clarify. steps.

      ss. rewrite points_to_split in A. rewrite <- GRA.embed_add in A. rewrite own_sep in A. iDestruct A. ss.

      acall_tac __ __ (@URA.unit Σ) (A0, A1) A; ss; et.
      { instantiate (2:=(_, _, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitR A; ss. et. }
      { esplits; ss. eauto with ord_step. }
      des; iRefresh. subst. rewrite Any.upcast_downcast. steps.

      acall_tac __ __ (@URA.unit Σ) (A0, POST) A1; ss; et.
      { instantiate (2:=(_, _, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitR A1; ss. et. }
      { esplits; ss. eauto with ord_step. }
      des; iRefresh. subst. rewrite Any.upcast_downcast. steps.

      astop. force_l. eexists.
      hret_tac (@URA.unit Σ) (A0, POST, POST0); ss.
      { esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. do 2 eexists; iRefresh. iSplitR A0; et. iSplitP; ss; et.
        rewrite points_to_split. rewrite <- GRA.embed_add. rewrite own_sep. iSplitL POST; ss.
      }
    }
  Qed.

End SIMMODSEM.
