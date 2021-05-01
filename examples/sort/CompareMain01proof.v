Require Import HoareDef CompareMain0 CompareMain1 Wrap1 CompareHeader SimModSemL SimModSem.
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
  Hypothesis CmpsStb_incl
    :
      forall fn skenv fsp
             (SPECS: List.find (fun '(_fn, _) => dec fn _fn) MainCmpsStb = Some fsp),
        List.find (fun '(_fn, _) => dec fn _fn) (CmpsStb skenv) = Some fsp.

  Hypotheses GlobalStb_wrap
    :
      forall skenv,
        List.find (fun '(_fn, _) => dec "wrap" _fn) (GlobalStb skenv) = Some ("wrap", wrap_spec CmpsStb skenv).

  Theorem correct: ModPair.sim (CompareMain1.Main GlobalStb) (CompareMain0.Main).
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf); et; ss.
    econs; ss; [|econs; ss].
    - init. unfold mainF, ccall. harg_tac. des; clarify.
      iRefresh. iDestruct PRE. iPure PRE. des; clarify.
      rewrite Any.upcast_downcast. ss. steps. astart 2.
      hexploit (@SKINCL "compare").
      { econs; ss. }
      i. des. rewrite H. steps.
      acall_tac (x0, x1, mycmp) (ord_pure 1) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ); ss.
      { eapply GlobalStb_wrap. }
      { ss. iRefresh. iSplitP; ss. r; esplits; eauto. red. esplits; eauto.
        { eapply SKWF. eauto. }
        { eapply CmpsStb_incl. des_ifs. }
      }
      ss. iRefresh. iDestruct POST. iPure POST. des;clarify.
      eapply Any.upcast_inj in POST. des; clarify. steps.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify. steps.
      acall_tac (x0, x1, mycmp) (ord_pure 1) (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ); ss.
      { eapply GlobalStb_wrap. }
      { ss. iRefresh. iSplitP; ss. r; esplits; eauto. red. esplits; eauto.
        { eapply SKWF. eauto. }
        { eapply CmpsStb_incl. des_ifs. }
      }
      ss. iRefresh. iDestruct POST. iPure POST. des;clarify.
      eapply Any.upcast_inj in POST. des; clarify. steps.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify. steps.
      astop. force_r; auto. steps.
      force_l. eexists. steps. hret_tac (@URA.unit Σ) (@URA.unit Σ); ss.
    - init. unfold compareF, ccall. harg_tac. des; clarify.
      destruct x as [n0 n1]. ss. iRefresh. iDestruct PRE. iPure PRE. des; clarify.
      rewrite Any.upcast_downcast. ss. steps. astart 0. astop.
      eapply Any.upcast_inj in PRE. des; clarify. steps.
      force_l. eexists. hret_tac (@URA.unit Σ) (@URA.unit Σ); ss.
  Qed.

End SIMMODSEM.
