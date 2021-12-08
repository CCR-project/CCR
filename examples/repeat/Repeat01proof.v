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

  Hypothesis FunStb_incl: forall sk,
      stb_incl (FunStb sk) (GlobalStb sk).

  Hypothesis GlobalStb_repeat: forall sk,
      fn_has_spec (GlobalStb sk) "repeat" (Repeat1.repeat_spec FunStb sk).

  Hypothesis GlobalStb_complete: forall sk fn,
      GlobalStb sk fn <> None.

  Theorem correct: refines2 [Repeat0.Repeat] [Repeat1.Repeat FunStb GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits; et. red. econs. eapply to_semantic. et. }
    econs; ss. unfold repeatF. init.
    { harg. destruct x as [[[f n] x] f_spec]. ss. mDesAll. des; clarify.
      steps. force_r; auto. des_ifs.
      { astop. steps. force_l. eexists. steps.
        hret _; ss.
        iPureIntro. splits; et. destruct n; et. exfalso. lia.
      }
      { destruct n.
        { exfalso. lia. }
        steps. inv PURE3. inv SPEC. rewrite FBLOCK. unfold ccallU. steps.
        astart 2. acatch.
        { eapply FunStb_incl. et. }
        hcall_weaken _ _ _ with ""; et.
        { splits; ss. eapply Ord.le_lt_lt.
          { eapply OrdArith.add_base_l. }
          { eapply OrdArith.lt_add_r. rewrite Ord.from_nat_S. eapply Ord.S_lt. }
        }
        ss. mDesAll. des; clarify.
        hexploit GlobalStb_repeat. i. inv H. steps. acatch.
        { et. }
        hcall_weaken (Repeat1.repeat_spec FunStb sk) (_, n, _, _) _ with ""; ss.
        { iPureIntro. esplits; et.
          { repeat f_equal. lia. }
          { unfold_intrange_64. unfold sumbool_to_bool in *. des_ifs; try lia. }
          { econs; et. econs; et. }
        }
        { splits; ss. eauto with ord_step. }
        mDesAll. des; clarify. steps.
        astop. steps. force_l. eexists. steps.
        hret _; ss.
      }
    }
    { harg. mDesAll. des; clarify. steps. }
    Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
