Require Import HoareDef Compare0 Compare1 SimModSemL SimModSem.
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

Require Import HTactics Logic YPM TODOYJ.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.




Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = (ε, tt↑)>>) /\
      (<<TGT: mrps_tgt0 = (ε, tt↑)>>)
  .

  Lemma cmpspecs_globalstb fn f
        (SPECS: cmpspecs fn = Some f)
        skenv        
        (SKINCL: Sk.incl Compare0.Compare.(Mod.sk) skenv)
        (SKWF: SkEnv.wf skenv)
    :
      exists fsp,
        (<<FIND: List.find (fun '(_fn, _) => dec fn _fn) (GlobalStb cmpspecs skenv) = Some (fn, fsp)>>) /\
        (<<SPEC: forall 


.
  Proof. 

fspec    

(*   PRE2 : SkEnv.blk2id skenv blk = Some fn0 *)
(*   PRE3 : cmpspecs fn0 = Some f *)
(*   EQ : list val = list val *)
(*   GWF : ☀ *)
(*   ============================ *)
(*   find (fun '(_fn, _) => dec fn0 _fn) (GlobalStb cmpspecs skenv) = Some (fn0, ?fsp) *)

(* Record fspec (Σ : GRA.t) : Type := mk *)
(*   { mn : string; *)
(*     X : Type; *)
(*     AA : Type; *)
(*     AR : Type; *)
(*     precond : X -> AA -> Any.t -> ord -> Σ -> Prop; *)
(*     postcond : X -> AR -> Any.t -> Σ -> Prop } *)


  Theorem correct: ModPair.sim (Compare1.Main cmpspecs) Compare0.Compare.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf); et; ss.
    econs; ss; [|econs; ss; [|econs; ss]].
    - init. unfold mainF, ccall. harg_tac. des; subst. iRefresh.
      rewrite Any.upcast_downcast. ss. steps. astart 10.
      hexploit (SKINCL "compare").
      { econs; ss. }
      i. des. rewrite H. ss. steps.
      acall_tac (x0, x1, mycmp) (ord_pure 1) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ); ss.
      { ss. esplits; eauto. red. esplits; eauto.
        - eapply SKWF. eauto.
        - ss. }
      des. iPure POST. clarify. eapply Any.upcast_inj in POST. des; clarify.
      steps. rewrite Any.upcast_downcast in _UNWRAPN. clarify. 
      steps.
      acall_tac (x0, x1, mycmp) (ord_pure 1) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ); ss.
      { ss. esplits; eauto. red. esplits; eauto.
        - eapply SKWF. eauto.
        - ss. }
      des. iPure POST. clarify. eapply Any.upcast_inj in POST. des; clarify.
      steps. rewrite Any.upcast_downcast in _UNWRAPN. clarify. 
      steps. astop. steps. force_l. eexists. force_r; auto. steps.
      hret_tac (@URA.unit Σ) (@URA.unit Σ); ss.
    - init. unfold compareF, ccall. harg_tac. des; subst. iRefresh.
      rewrite Any.upcast_downcast. ss. steps. 
      ss. iPure PRE. des; clarify. 
      apply Any.upcast_inj in PRE. des; clarify. steps.
      astart 0. astop. force_l. eexists.
      hret_tac (@URA.unit Σ) (@URA.unit Σ); ss.
    - init. unfold wrapF, ccall. harg_tac.
      destruct x as [[n0 n1] f]. ss. des. red in PRE. des; clarify.
      eapply Any.upcast_inj in PRE0. des; clarify.
      rewrite Any.upcast_downcast. ss. steps. rewrite PRE2. steps. astart 1.

      rename fn into fn0.

      eapply APC_step_clo with (fn:=fn0) (args:=[Vint n0; Vint n1]);
        [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
         (try by (stb_tac; refl))|
         (try refl)|
         (eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r)|
         (let args := fresh "args" in
          let EQ := fresh "EQ" in
          intros args EQ)].
      { 



astep fn (Any.upcast [Vint n0; Vint n1]).

Ltac astep _fn _args :=


      rewrite _APC.

eapply 

      acall_tac tt (ord_pure 1) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ); ss.


      astart 1.

      astart 0. astop. rewrite PRE2. force_l. eexists. steps.

  ss.

des; subst. iRefresh.
      rewrite Any.upcast_downcast. ss. steps. 
      ss. iPure PRE. des; clarify. 
      apply Any.upcast_inj in PRE. des; clarify. steps.
      astart 0. astop. force_l. eexists.
      hret_tac (@URA.unit Σ) (@URA.unit Σ); ss.


    -       hret_tac

 steps.

astop.
      

ss. steps. 

iDestruct PRE.
astart 10.
      hexploit (SKINCL "compare").
      { econs; ss. }
      i. des. rewrite H. ss. steps.
      acall_tac (x0, x1, mycmp) (ord_pure 1) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ); ss.
      { ss. esplits; eauto. red. esplits; eauto.
        - eapply SKWF. eauto.
        - ss. }
      des. iPure POST. clarify. eapply Any.upcast_inj in POST. des; clarify.
      steps. rewrite Any.upcast_downcast in _UNWRAPN. clarify. 
      steps.
      acall_tac (x0, x1, mycmp) (ord_pure 1) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ); ss.
      { ss. esplits; eauto. red. esplits; eauto.
        - eapply SKWF. eauto.
        - ss. }
      des. iPure POST. clarify. eapply Any.upcast_inj in POST. des; clarify.
      steps. rewrite Any.upcast_downcast in _UNWRAPN. clarify. 
      steps. astop. steps. force_l. eexists. force_r; auto. steps.
      hret_tac (@URA.unit Σ) (@URA.unit Σ); ss.


__ PRE.
      
hret_tac

      steps.

      astop.
      steps.

      steps.
      steps.


      iDes POST.

      steps.

 ss.

      r
 anytac.


econs; ss.  ii. init.

admit "". admit "". econs. init. unfold ccall.
    harg_tac. des; clarify. unfold fF, ccall. anytac. ss.
    steps. astart 10. destruct (dec (Z.of_nat x) 0%Z).
    - destruct x; ss. astop.
      force_l. eexists. hret_tac (@URA.unit Σ) (@URA.unit Σ).
      { esplits; eauto. }
      { split; auto. }
    - destruct x; [ss|]. rewrite Nat2Z.inj_succ. steps.
      acall_tac x (ord_pure x) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ).
      { replace (Z.succ (Z.of_nat x) - 1)%Z with (Z.of_nat x) by lia. ss. }
      { splits; ss. auto with ord_step. }
      { split; auto. }
      des. subst. anytac. asimpl. steps. astop.
      force_l. eexists. hret_tac (@URA.unit Σ) (@URA.unit Σ).
      { splits; auto. unfold sum. splits; auto. ss. repeat f_equal. lia. }
      { split; ss. }
  Qed.

End SIMMODSEM.
