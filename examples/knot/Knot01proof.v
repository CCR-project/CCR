Require Import HoareDef Knot0 Knot1 SimModSemL SimModSem.
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
  Context `{@GRA.inG knotRA Σ}.

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ) (f: option (nat -> nat)),
        (<<SRC: mrps_src0 = (mr, tt↑)>>) /\
        (<<TGT: mrps_tgt0 = (ε, f↑)>>) /\
        (<<SIM: (iHyp (Own (GRA.embed (bw_full (Z.odd n)))) mr)>>)
  .


  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = (ε, tt↑)>>) /\
      (<<TGT: mrps_tgt0 = (ε, tt↑)>>)
  .

  Variable RecStb: SkEnv.t -> list (gname * fspec).
  Variable FunStb: SkEnv.t -> list (gname * fspec).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Variable RecStb_incl
    :
      forall skenv fn fsp
             (SPECS: List.find (fun '(_fn, _) => dec fn _fn) KnotRecStb = Some fsp),
        List.find (fun '(_fn, _) => dec fn _fn) (RecStb skenv) = Some fsp.

  Variable FunStb_incl
    :
      forall skenv fn fsp
             (SPECS: List.find (fun '(_fn, _) => dec fn _fn) (FunStb skenv) = Some fsp),
        List.find (fun '(_fn, _) => dec fn _fn) (GlobalStb skenv) = Some fsp.

  Theorem correct: ModPair.sim (Knot1.Knot RecStb FunStb GlobalStb) Knot0.Knot.
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
    hexploit CmpsStb_incl; eauto. i. des.
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
