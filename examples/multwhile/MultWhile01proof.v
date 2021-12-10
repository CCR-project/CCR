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
  Let Inv := (fun (_: unit) (_ _: Any.t) => (True: iProp)%I).

  Definition to_irel (R_src R_tgt: Type)
             (RR: R_src -> R_tgt -> Any.t -> Any.t -> iProp)
             (st_src: Any.t) (st_tgt: Any.t)
             (r_src: R_src) (r_tgt: R_tgt): Prop :=
    exists mr_src mp_src,
      (<<SRC: st_src = Any.pair mp_src (Any.upcast mr_src)>>) /\
      (<<IPROP: RR r_src r_tgt mp_src st_tgt mr_src>>).

  Lemma hbind_clo
        A (a: shelve__ A)
        mn r rg n m mr_src mp_src a0
        X (Q: option mname -> X -> Any.t -> Any.t -> Σ -> Prop)
        x vret_src vret_tgt
        mp_tgt
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (R_src0 R_tgt0 R_src1 R_tgt1: Type)
        (RR: R_src0 -> R_tgt0 -> Any.t -> Any.t -> iProp)

        (itr_src: itree Es (Σ * R_src0)) (ktr_src: (Σ * R_src0) -> itree Es R_src1)
        (itr_tgt: itree Es R_tgt) (ktr_tgt: R_tgt0 -> itree Es R_tgt1)

        ctx l
        (ACC: current_iPropL ctx l)

        (WLE: le a0 a)

        (UPDATABLE:
           (from_iPropL l) ⊢ #=> (R a mp_src mp_tgt ** (Q mn x vret_src vret_tgt: iProp)))

        (LEFT: gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le))
                      r rg _ _ (to_irel RR) m n a0
                      (Any.pair mp_src mr_src, itr_src)
                      (mp_tgt, itr_tgt))
        (LEFT: forall mr_src mp_src mp_tgt r_src r_tgt
                      (RR: RR mp_src mp_tgt r_src r_tgt

gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le))
                      r rg _ _ RR m n a0
                      (Any.pair mp_src mr_src, itr_src)
                      (mp_tgt, itr_tgt))


        (EQ: forall (mr_src1: Σ) (WLE: le a0 a) (WF: mk_wf R a (Any.pair mp_src mr_src1↑, mp_tgt)),
            eqr (Any.pair mp_src mr_src1↑) mp_tgt vret_tgt vret_tgt)
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le))
             r rg _ _ eqr m n a0
             (Any.pair mp_src mr_src, itr_src >>= ktr_src)
             (mp_tgt, itr_tgt >>= ktr_tgt)
  .
  Proof.
    subst. unfold HoareFunRet, mput, mget, guarantee.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists vret_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs).
    assert (exists mr_src1 rret_src,
               (<<UPDATABLE: URA.wf (ctx ⋅ (mr_src1 ⋅ rret_src))>>) /\
               (<<RSRC: R a mp_src mp_tgt mr_src1>>) /\
               (<<PRE: Q mn x vret_src vret_tgt rret_src>>)).
    { red in ACC. inv ACC. uipropall.
      hexploit (UPDATABLE r0); et.
      { eapply URA.wf_mon; et. }
      i. des. subst. exists a1, b. splits; et.
      replace (ctx ⋅ (a1 ⋅ b)) with (a1 ⋅ b ⋅ ctx); et.
      r_solve.
    }
    des. exists (rret_src, mr_src1).
    repeat (ired_both; apply sim_itreeC_spec; econs).
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits.
    { r_wf UPDATABLE0. }
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    repeat (ired_both; apply sim_itreeC_spec; econs).
    eapply EQ; et. econs; et.
  Qed.


  Theorem correct: refines2 [MultWhile0.Mul] [MultWhile1.Mul].
  Proof.
    (* boring part *)
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=mk_wf Inv) (le:=top2); et.
    { ss. }
    2: { exists tt. unfold Inv. econs; ss; red; uipropall. }
    econs; ss. unfold mulF, ccallU. init. harg.

    destruct x as [a b]. mDesAll. des; clarify. simpl. steps. astop. simpl. steps.
    (* bind *)
    guclo lbindC_spec. eapply lbindR_intro with (RR := fun st_src _ r_src r_tgt => r_src = r_tgt↑ /\ r_tgt = (a * b)%Z /\ st_src = Any.pair mp_src (Any.upcast mr_src)).
    { steps. instantiate (1:=tt).
      (* induction on a *)
      assert (exists n, <<EQ: a = Z.of_nat n>> /\ <<SUM: (a * b + 0 = a * b)%Z>>).
      { exists (Z.to_nat a). rewrite Z2Nat.id; auto. splits; auto. lia. }
      des. deflag. revert EQ SUM. generalize a at 1 2 5. generalize 0%Z at 1 3. induction n; i.
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
