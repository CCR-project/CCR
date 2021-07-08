Require Import HoareDef OpenDef STB Repeat0 Repeat1 SimModSem.
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

  Hypothesis FunStb_incl: forall skenv,
      stb_incl (FunStb skenv) (GlobalStb skenv).

  Hypothesis GlobalStb_repeat: forall skenv,
      fn_has_spec (GlobalStb skenv) "repeat" (Repeat1.repeat_spec FunStb skenv).

  Theorem correct: refines2 [Repeat0.Repeat] [Repeat1.Repeat FunStb GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits; et. red. econs. eapply to_semantic. et. }
    econs; ss.
    kinit.
    2: { harg. mDesAll. des; clarify. steps. }
    harg. destruct x as [[[f n] x] f_spec]. ss. mDesAll. des; clarify.
    steps. unfold Repeat0.repeat.
    rewrite unfold_eval_imp. imp_steps.
    des_ifs.
    2: { exfalso. apply n0. solve_NoDup. }
    imp_steps. des_ifs.
    { imp_steps. astart 0. astop. steps. force_l. eexists. steps.
      hret _; ss.
      iPureIntro. splits; et. destruct n; et. exfalso. lia.
    }
    { destruct n.
      { exfalso. lia. }
      imp_steps. inv PURE4. inv SPEC. rewrite FBLOCK. imp_steps.
      astart 2. acatch.
      { eapply FunStb_incl. et. }
      hcall_weaken _ _ _ _ with ""; et.
      { splits; ss. eapply Ord.le_lt_lt.
        { eapply OrdArith.add_base_l. }
        { eapply OrdArith.lt_add_r. rewrite Ord.from_nat_S. eapply Ord.S_lt. }
      }
      ss. mDesAll. des; clarify. imp_steps.
      guclo lordC_spec. econs.
      { instantiate (5:=100). eapply OrdArith.add_base_l. }
      hexploit GlobalStb_repeat. i. inv H. acatch.
      { et. }
      hcall_weaken (Repeat1.repeat_spec FunStb sk) _ (_, n, _, _) _ with ""; ss.
      { iPureIntro. esplits; et.
        { repeat f_equal. lia. }
        { unfold intrange_64, sumbool_to_bool in *. des_ifs; try lia. }
        { econs; et. econs; et. }
      }
      { splits; ss. eauto with ord_step. }
      mDesAll. des; clarify. steps.
      guclo lordC_spec. econs.
      { instantiate (5:=100). eapply OrdArith.add_base_l. }
      astop. steps. force_l. eexists. imp_steps.
      hret _; ss.
    }
    Unshelve. all:ss. all:try (exact 0).
  Qed.

End SIMMODSEM.
