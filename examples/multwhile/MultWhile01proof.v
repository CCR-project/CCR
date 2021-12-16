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

Require Import HTactics ProofMode HSim.

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

  Theorem correct: refines2 [MultWhile0.Mul] [MultWhile1.Mul].
  Proof.
    (* boring part *)
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=mk_wf Inv) (le:=top2); et.
    { ss. }
    2: { exists tt. unfold Inv. econs; ss; red; uipropall. }
    econs; ss. unfold mulF, ccallU. init. harg.
    mDesAll. des_ifs. gfinal. right.    
    hexploit (@hsim_adequacy_aux _ unit top2 Inv "Mul" (STB.to_stb Mulstb) (ord_pure n) true false (mp_src) mp_tgt).
    2:{ i. instantiate (8:=None) in H.
        instantiate (4:=ctx) in H.
        instantiate (4:=(z, z0)) in H.
        instantiate (4:=mn) in H.
        instantiate (4:=Any.upcast mr_src) in H.
        instantiate (4:=w) in H.
        instantiate (1:=    ` varg0 : Z * Z <- unwrapU (Any.downcast varg);;
                                      ` vret : Z <-
                                               (let
                                                   '(a, b) := varg0 in
                                                 ITree.iter (λ '(a0, res), if (0 <? a0)%Z then Ret (inl ((a0 - 1)%Z, (res + b)%Z)) else Ret (inr res)) (a, 0%Z));;
                                               Ret (Any.upcast vret)) in H.
        ss.
        match goal with
        | H: ?P0 |- ?P1 => replace P1 with P0
        end.
        { eapply H. }
        f_equal. f_equal. ss. f_equal. f_equal.

        instantiate (6:=ctx).



        instantiate (1:=(APC;; trigger (Choose Any.t))) in H.

        ss.


        eapply H. mDesAll. des; clarify.


        instantiate (4:=w) in H.
        instantiate (8:=None) in H.
        instantiate (7:=None) in H.

 ss.
        instantiate (2:=x) in H.


hsim_adequacy_aux
     : ∀ (world : Type) (le : relation world) (I : world → Any.t → Any.t → iProp) (mn : string) (stb : string → option fspec) 
         (o : ord) (f_src f_tgt : bool) (st_src st_tgt : Any.t) (itr_src : itree (hAPCE +' Es) Any.t) (itr_tgt : itree Es Any.t) 
         (mr_src : Any.t) (ctx : Σ) (X : Type) (x : X) (Q : option string → X → Any.t → Any.t → iProp) (mn_caller : option string) 
         (fuel : option Ord.t) (w0 : world),
         hsim I mn stb o (st_tgt, itr_tgt)
         → paco8 (_sim_itree (mk_wf I) le) bot8 Any.t Any.t (lift_rel (mk_wf I) le w0 eq) f_src f_tgt w0
             (Any.pair st_src mr_src, mylift mn stb o fuel mn_caller x ctx Q itr_src) (st_tgt, itr_tgt)


        match goal with
        | H: ?P0 |- ?P1 => replace P1 with P0
        end.
        { eapply H. }
        instantiate (6:=ctx).

        eapply f_equal.

        f_equal.
        
eapply f_equal.
        repeat f_equal.


        2:{ 

eapply H.

hsim_adequacy_aux
     : ∀ (world : Type) (le : relation world) (I : world → Any.t → Any.t → iProp) (mn : string) (stb : string → option fspec) 
         (o : ord) (f_src f_tgt : bool) (st_src st_tgt : Any.t) (itr_src : itree (hAPCE +' Es) Any.t) (itr_tgt : itree Es Any.t) 
         (mr_src : Any.t) (ctx : Σ) (X : Type) (x : X) (Q : option string → X → Any.t → Any.t → iProp) (mn_caller : option string) 
         (fuel : option Ord.t) (w0 : world),
         hsim I mn stb o (st_tgt, itr_tgt)
         → paco8 (_sim_itree (mk_wf I) le) bot8 Any.t Any.t (lift_rel (mk_wf I) le w0 eq) f_src f_tgt w0
             (Any.pair st_src mr_src, mylift mn stb o fuel mn_caller x ctx Q itr_src) (st_tgt, itr_tgt)


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
