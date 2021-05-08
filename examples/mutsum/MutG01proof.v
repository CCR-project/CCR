Require Import HoareDef MutHeader MutG0 MutG1 SimModSem.
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

Require Import HTactics Logic YPM.

Set Implicit Arguments.

Local Open Scope nat_scope.



(* TODO: move to SimModSem & add cpn3_wcompat *)
Hint Resolve sim_itree_mon: paco.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).

  Let wf: W -> Prop :=
    mk_wf (fun (_: unit) _ => (True: iProp)%I) (fun _ _ => (True: iProp)%I).

  Theorem correct: ModPair.sim MutG1.G MutG0.G.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf); et.
    2: { econs; ss; red; uipropall. }
    econs; ss. init. harg. mDesAll.
    des; clarify. unfold gF, ccall.
    apply Any.upcast_inj in PURE0. des; clarify.
    rewrite Any.upcast_downcast. steps. astart 10.
    destruct (dec (Z.of_nat x) 0%Z).
    - destruct x; ss. astop. force_l. eexists.
      hret _; ss.
    - destruct x; [ss|]. rewrite Nat2Z.inj_succ. steps. acatch.
      hcall _ _ _ with "*".
      { ss. }
      { iPureIntro. splits; eauto.
        replace (Z.succ (Z.of_nat x) - 1)%Z with (Z.of_nat x) by lia. ss. }
      { splits; ss; eauto with ord_step. }
      i. mDesAll. des; clarify. eapply Any.upcast_inj in PURE2. des; clarify.
      rewrite Any.upcast_downcast. steps. astop.
      force_l. eexists.
      (* hret_tac begin *)
      eapply hret_clo.
      { et. }
      { eauto with ord_step. }
      { eassumption. }
      (* hret_tac end *)
      { ss. }
      { start_ipm_proof. iPureIntro. splits; ss.
        f_equal. f_equal. lia. }
      { i. ss. }
      Unshelve. all: ss.
  Qed.

End SIMMODSEM.
