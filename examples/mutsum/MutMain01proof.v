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

Require Import HTactics Logic.

Set Implicit Arguments.

Local Open Scope nat_scope.




Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Let wf: W -> Prop :=
    mk_wf (fun (_: unit) _ => (True: iProp)%I) (fun _ _ _ => True).

  Theorem correct: ModPair.sim MutMain1.Main MutMain0.Main.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf); et; ss.
    2: { red. econs; ss. red. uipropall. }
    econs; ss. init.
    unfold mainF, mainBody.
    (* harg_tac begin *)
    eapply (@harg_clo _ "H" "INV"); [eassumption|]. clear SIMMRS mrs_src mrs_tgt. i.
    (* harg_tac end*)
    mDesAll. des; clarify. steps. rewrite Any.upcast_downcast. steps.

    (* hcall_tac begin *)
    eapply hcall_clo with (Rn:="H") (Invn:="INV") (Hns := []).
    { admit "fix". }
    { et. }
    { admit "fix". }
    { start_ipm_proof. iPureIntro. splits; eauto. instantiate (1:=10). ss. }
    { eauto with ord_step. }
    { splits; ss. }
    clear ACC ctx. i.
    mDesAll. des; clarify. eapply Any.upcast_inj in PURE2. des; clarify. steps.
    (* hret_tac begin *)
    eapply hret_clo.
    { et. }
    { eauto with ord_step. }
    { eassumption. }
    (* hret_tac end *)
    { ss. }
    { start_ipm_proof.
      (* TODO: change top2 => pure top in SMod.main *)
      iModIntro. repeat iSplit; ss.
      iStopProof. red. uipropall. }
    { i. ss. }
  Qed.

End SIMMODSEM.
