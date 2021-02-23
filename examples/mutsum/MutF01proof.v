Require Import MutHeader MutF0 MutF1 SimModSem Hoare.
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
          lookup "F" (fst w) = Some (mn_src, mr_src)) /\
      (exists mn_tgt mr_tgt,
          lookup "F" (snd w) = Some (mn_tgt, mr_tgt))
  .

  Theorem correct: ModSemPair.sim MutF1.FSem MutF0.FSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    2: { split; ss; et. }
    econs; ss. econs; ss. ii. subst.
    exists 100. ss. unfold fF, fun_to_tgt, HoareFun. ss.
    unfold forge, checkWf, body_to_tgt, assume.
    inv SIMMRS. des. repeat go. des. clarify.
    eapply f_equal with (f:=@Any.downcast (list val)) in x5.
    repeat rewrite Any.upcast_downcast in *. clarify.
    unfold APC, interp_hCallE_tgt, put, discard, guarantee.
    ired. des_ifs.
    - destruct x0; ss. repeat rewrite interp_trigger.
      go. exists 0. left. repeat go.
      repeat rewrite interp_trigger. repeat go. eexists. left.
      repeat go. eexists. left.
      repeat go. eexists (_, _). left. repeat go. esplits; [refl|]. left.
      repeat go. eexists. left. go. esplits; et. left.
      repeat go. eexists. left. repeat go. esplits; et. left. repeat go.
      split; esplits; ss; et.
    - destruct x0; [ss|]. rewrite Nat2Z.inj_succ.
      repeat rewrite interp_trigger.
      go. exists 1. left. repeat go.
      repeat rewrite interp_trigger.
      go. eexists ("g", [Vint (Z.of_nat x0)]↑). left.
      repeat go. repeat rewrite interp_trigger. cbn. ss.
      unfold HoareCall, put, discard, forge, checkWf, assume, guarantee.
      rewrite Any.upcast_downcast. repeat go.
      eexists (_, _). left. repeat go. esplits; [refl|]. left.
      repeat go. eexists _. left. repeat go. eexists. left.
      repeat go. esplits; et. left. repeat go. esplits; et. left.
      replace (Z.succ (Z.of_nat x0) - 1)%Z with (Z.of_nat x0).
      2: { lia. }
      repeat go. eexists. left. repeat go. esplits; et. left.
      repeat go. esplits; et. left. repeat go. esplits; ss. left.
      repeat go.
      { split; esplits; ss; eauto. }
      exists 100. left. inv WF. des.
      repeat go. des; clarify.
      eapply f_equal with (f:=@Any.downcast val) in x6.
      repeat rewrite Any.upcast_downcast in *. clarify.
      eexists. left. subst. repeat go.
      eexists. left. repeat go.
      eexists (_, _). left. repeat go.
      esplits; [refl|]. left. repeat go.
      eexists. left. repeat go. esplits; et. left.
      repeat go. eexists. left. repeat go. esplits; et. left.
      repeat go.
      replace (Z.succ (Z.of_nat x0) + Z.of_nat (sum x0))%Z with (Z.of_nat (sum (S x0))).
      2: { Local Transparent sum. ss. lia. }
      go. split; esplits; ss; eauto.
  Qed.

End SIMMODSEM.
