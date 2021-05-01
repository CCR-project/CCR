Require Import HoareDef Wrap0 Wrap1 CompareHeader SimModSemL SimModSem.
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

  Variable CmpsStb: SkEnv.t -> list (gname * fspec).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  (* TODO: define alist inclusion relation *)
  Variable CmpsStb_incl
    :
      forall skenv fn fsp
             (SPECS: List.find (fun '(_fn, _) => dec fn _fn) (CmpsStb skenv) = Some fsp),
        List.find (fun '(_fn, _) => dec fn _fn) (GlobalStb skenv) = Some fsp.

  Theorem correct: ModPair.sim (Wrap1.Wrap CmpsStb GlobalStb) Wrap0.Wrap.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf); et; ss.
    econs; ss. init. unfold wrapF, ccall. harg_tac.
    destruct x as [[n0 n1] f]. ss. des; subst.
    iRefresh. iDestruct PRE. iPure PRE. des; clarify.
    eapply Any.upcast_inj in PRE. des; clarify.
    rewrite Any.upcast_downcast. ss. steps. astart 1.
    rewrite PRE1. ss. steps. rename fn into fn0.
    acall_tac (n0, n1) (ord_pure 0) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ); ss.
    { eapply CmpsStb_incl. eauto. }
    { ss. }
    { ss. splits; ss. eauto with ord_step. }
    ss. iRefresh. iDestruct POST. iPure POST. clarify. eapply Any.upcast_inj in POST. des; clarify.
    steps. rewrite Any.upcast_downcast in _UNWRAPN. clarify. astop.
    force_l. eexists.
    hret_tac (@URA.unit Σ) (@URA.unit Σ); ss.
  Qed.

End SIMMODSEM.
