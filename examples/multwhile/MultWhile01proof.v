Require Import HoareDef MultWhile0 MultWhile1 SimModSem.
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

Require Import HTactics ProofMode.

Set Implicit Arguments.

Local Open Scope nat_scope.



Notation "wf RR f_src f_tgt r g '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco8 (_sim_itree wf _) _ r g _ _ RR f_src f_tgt _ ((Any.pair src0 src1), src2) (tgt0, tgt2))
      (at level 60,
       format "wf '//' RR '//' f_src  f_tgt '//' r  g '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Notation "wf RR f_src f_tgt r g '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco8 (_sim_itree wf _) _ r g _ _ RR f_src f_tgt _ (src0, src2) (tgt0, tgt2))
      (at level 60,
       format "wf '//' RR '//' f_src  f_tgt '//' r  g '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Lemma unfold_iter E A B (f: A -> itree E (A + B)) (x: A)
  :
    ITree.iter f x =
    lr <- f x;;
    match lr with
    | inl l => tau;; ITree.iter f l
    | inr r => Ret r
    end.
Proof.
  apply bisim_is_eq. eapply unfold_iter.
Qed.

Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  (* trivial invariant *)
  Let wf := mk_wf (fun (_: unit) _ _ => (True: iProp)%I).

  Theorem correct: refines2 [MultWhile0.Mul] [MultWhile1.Mul].
  Proof.
    (* boring part *)
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et.
    { ss. }
    2: { exists tt. econs; ss; red; uipropall. }
    econs; ss. unfold mulF, ccallU. init. harg.

    destruct x as [a b]. mDesAll. des; clarify. steps. astop. steps.
    guclo lbindC_spec. eapply lbindR_intro with (RR := fun st_src _ r_src r_tgt => r_src = r_tgt↑ /\ r_tgt = (a * b)%Z /\ st_src = Any.pair mp_src (Any.upcast mr_src)).
    { steps. deflag. instantiate (1:=tt).
      (* induction on a *)
      assert (exists n, <<EQ: a = Z.of_nat n>> /\ <<SUM: (a * b + 0 = a * b)%Z>>).
      { exists (Z.to_nat a). rewrite Z2Nat.id; auto. splits; auto. lia. }
      des. revert EQ SUM. generalize a at 1 2 5. generalize 0%Z at 1 3. induction n; i.
      (* a = 0 *)
      { rewrite unfold_iter. subst. ss. steps. force_l. eexists. steps. }
      (* a = S _ *)
      { rewrite unfold_iter. subst. ss. steps. deflag. eapply IHn.
        { lia. }
        { lia. }
      }
    }
    { i. des. clarify. steps. hret tt; auto. }
  Qed.

End SIMMODSEM.
