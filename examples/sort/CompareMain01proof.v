Require Import HoareDef CompareMain0 CompareMain1 CompareHeader SimModSemL SimModSem.
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

  Variable global_cmpspecs: list (gname * (Z -> Z -> Z)).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Variable cmpspecs_incl: 
    forall fn fd
           (FIND: List.find (fun '(_fn, _) => dec fn _fn) cmpspecs = Some fd),
      List.find (fun '(_fn, _) => dec fn _fn) global_cmpspecs = Some fd.

  Variable globalstb_incl
    :
      forall skenv fn f fn'
             (SPECS: List.find (fun '(_fn, _) => dec fn _fn) cmpspecs = Some (fn', f)),
      exists mn,
        (<<FIND: List.find (fun '(_fn, _) => dec fn _fn) (GlobalStb skenv) = Some (fn, compare_gen f mn)>>).

  Variable cmpspecs_globalstb
    :
      forall skenv fn f fn'
             (SPECS: List.find (fun '(_fn, _) => dec fn _fn) cmpspecs = Some (fn', f)),
      exists mn,
        (<<FIND: List.find (fun '(_fn, _) => dec fn _fn) (GlobalStb skenv) = Some (fn, compare_gen f mn)>>).

  Theorem correct: ModPair.sim (Wrap1.Wrap cmpspecs GlobalStb) Wrap0.Wrap.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf); et; ss.
    econs; ss. init. unfold wrapF, ccall. harg_tac. 
    destruct x as [[n0 n1] f]. ss. des; subst. 
    iPure PRE. des; clarify.
    eapply Any.upcast_inj in PRE. des; clarify.
    rewrite Any.upcast_downcast. ss. steps. astart 1.
    rewrite PRE1. ss. steps. rename fn into fn0. 
    hexploit cmpspecs_globalstb; eauto. i. des.
    eapply APC_step_clo with (fn:=fn0) (args:=[Vint n0; Vint n1]).
    { try by
      eapply Ord.eq_lt_lt;
       [ symmetry; eapply OrdArith.add_from_nat
       | eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r;
          eapply Nat.lt_succ_diag_r ]. }
    { eauto. }
    { ss. }
    { eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r. }
    i. subst args'. 
    hcall_tac (n0, n1) (ord_pure 0) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ); ss.
    { splits; ss. eauto with ord_step. }
    des. iPure POST. clarify. eapply Any.upcast_inj in POST. des; clarify.
    steps. rewrite Any.upcast_downcast in _UNWRAPN. clarify. astop. 
    force_l. eexists.
    hret_tac (@URA.unit Σ) (@URA.unit Σ); ss.
  Qed.

End SIMMODSEM.
