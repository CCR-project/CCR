Require Import HoareDef MutHeader MutGImp MutG0 SimModSem.
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

Require Import HTactics.
Require Import TODO.

Require Import Imp.
Import ImpNotations.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = Maps.add "G" (ε, tt↑) Maps.empty>>) /\
      (<<TGT: mrps_tgt0 = Maps.add "G" (ε, tt↑) Maps.empty>>)
  .

  Theorem correct: ModSemPair.sim MutG0.GSem MutGImp.GSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss. init. unfold cfun.
    unfold gF.
    unfold MutGImp.gF.
    Local Opaque vadd.
    steps.
    rewrite eval_imp_unfold.
    ss.
    eapply Any.downcast_upcast in _UNWRAPN. des. clarify.
    unfold unint in *. ss.
    imp_steps.
    des_ifs.
    - imp_steps.
    - apply Z.eqb_eq in Heq0. apply n in Heq0. inversion Heq0.
    - unfold ccall.
      imp_steps.
      gstep. econs; ss. i. des; subst. exists 100.
      imp_steps.
      rewrite _UNWRAPU. imp_steps.
  Qed.

End SIMMODSEM.
