Require Import HoareDef MutHeader MutFImp MutF0 SimModSem.
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

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Local Opaque GRA.to_URA.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = Maps.add "F" (ε, tt↑) Maps.empty>>) /\
      (<<TGT: mrps_tgt0 = Maps.add "F" (ε, tt↑) Maps.empty>>)
  .

  Theorem correct: ModSemPair.sim MutF0.FSem MutFImp.FSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss. init. unfold cfun. unfold fF.
    unfold Imp.eval_function.
    ired_all. ss. steps.
    eapply Any.downcast_upcast in _UNWRAPN. des. clarify.
    unfold unint in *. ss. des_ifs.
    - ired_all.
      (* unfold interp_function. grind. unfold ImpNotations.Vint_coerce. steps. *)
      rewrite interp_function_bind.
      rewrite interp_function_GetVar. steps.
      rewrite interp_function_bind.
      rewrite interp_function_ret. steps.
      rewrite interp_function_ret. steps.
    - unfold ccall. steps.
      admit "lemmas for imp...".
  Qed.

(** tau, trigger, assume, guarantee, unwrap *)
  
End SIMMODSEM.
