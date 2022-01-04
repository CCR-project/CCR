Require Import HoareDef OpenDef STB Repeat1 Add0 Add1 SimModSem.
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

Require Import HTactics ProofMode Invariant.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Set Implicit Arguments.

Local Open Scope nat_scope.





Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Variable FunStb: Sk.t -> gname -> option fspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ _ _ => True%I)
  .

  Hypothesis FunStb_succ: forall skenv,
      fn_has_spec (FunStb skenv) "succ" (Add1.succ_spec).

  Hypothesis GlobalStb_repeat: forall skenv,
      fn_has_spec (GlobalStb skenv) "repeat" (Repeat1.repeat_spec FunStb skenv).

  Theorem correct: refines2 [Add0.Add] [Add1.Add GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits; et. red. econs. eapply to_semantic. et. }
    eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF.
    hexploit (SKINCL "succ"); ss; eauto. intros [blk0 FIND0].
    econs; ss.
    { unfold succF. init.
      2: { harg. mDesAll. des; clarify. steps. hret _; ss. }
      harg. mDesAll. des; clarify.
      steps. astart 0. astop. steps. force_l. eexists.
      steps. hret _; ss.
    }
    econs; ss.
    { unfold addF, add_body. init. harg. mDesAll. des; clarify.
      steps.  rewrite FIND0. steps. unfold ccallU. steps.
      hexploit FunStb_succ. i. inv H.
      assert (exists m, z0 = Z.of_nat m).
      { exists (Z.to_nat z0). rewrite Z2Nat.id; auto. lia. } des. subst.
      hexploit GlobalStb_repeat; et. i. inv H. astart 1. acatch; et.
      hcall_weaken (Repeat1.repeat_spec FunStb sk) (_, _, _, Z.succ) _ with ""; et.
      { iPureIntro. splits; et. econs.
        { eapply SKWF. eauto. }
        econs.
        { et. }
        { etrans; [|et]. econs. ss. esplits; ss; et. eapply Ord.lt_le. eapply Ord.omega_upperbound. }
      }
      { splits; ss. }
      mDesAll. des; clarify. steps. astop. steps. hret _; ss.
      iPureIntro. esplits; et.
      f_equal. f_equal. clear. generalize z. induction m; ss; i.
      { lia. }
      { rewrite <- IHm. lia. }
    }
    Unshelve. all:ss. all:try (exact 0).
  Qed.

End SIMMODSEM.
