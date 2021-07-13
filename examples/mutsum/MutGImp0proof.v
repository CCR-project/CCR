Require Import HoareDef MutHeader MutGImp MutG0 SimModSem.
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

Require Import HTactics.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Set Implicit Arguments.

Local Open Scope nat_scope.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Let wf: unit -> W -> Prop :=
    fun _ '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = tt↑>>) /\
      (<<TGT: mrps_tgt0 = tt↑>>)
  .

  Theorem correct:
    refines2 [MutGImp.G] [MutG0.G].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss. init. unfold cfunU.
    unfold gF.
    unfold MutGImp.gF.
    Local Opaque vadd.
    steps.
    rewrite unfold_eval_imp.
    (* eapply Any.downcast_upcast in _UNWRAPN. des. *)
    unfold unint in *. destruct v; clarify; ss.
    des_ifs.
    2: exfalso; apply n; solve_NoDup.
    3:{ exfalso; apply n0; solve_NoDup. }
    - imp_steps. red. esplits; et.
    - unfold ccallU.
      imp_steps. replace (z =? 0)%Z with false.
      2:{ symmetry. eapply Z.eqb_neq. auto. }
      imp_steps.
      rewrite _UNWRAPU1. steps. imp_steps. red. esplits; et.
    Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
