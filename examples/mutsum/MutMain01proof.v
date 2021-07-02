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

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    mk_wf (fun (_: unit) _ _ => (True: iProp)%I).

  Theorem correct: ModPair.sim MutMain1.Main MutMain0.Main.
  Proof.
    econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et.
    { ss. }
    2: { exists tt. red. econs; ss. red. uipropall. }
    econs; ss. init.
    unfold mainF, mainBody. harg.
    mDesAll. des; clarify. steps.
    astart 10. acatch. hcall _ _ tt with "*"; ss.
    { iPureIntro. esplits; eauto.
      { instantiate (1:=10). ss. }
      { unfold mut_max. lia. }
    }
    { splits; ss. }
    steps. astop. mDesAll. des; clarify. steps.
    hret tt; ss.
  Qed.

End SIMMODSEM.
