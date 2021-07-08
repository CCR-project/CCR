Require Import HoareDef OpenDef STB AddImp Add0 SimModSem.
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

  Let wf: _ -> W -> Prop := fun (_: unit) _ => True.

  Theorem correct: refines2 [AddImp.Add] [Add0.Add].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits; et. red. ss. }
    econs; ss.
    { init. u


    eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF.
    hexploit (SKINCL "succ"); ss; eauto. intros [blk0 FIND0].
    econs; ss.
    { kinit.
      2: { harg. mDesAll. des; clarify. steps. }
      harg. mDesAll. des; clarify.
      steps. astart 0. astop. force_l. eexists.
      unfold Add0.succ. rewrite unfold_eval_imp. imp_steps.
      des_ifs.
      2: { exfalso. apply n. solve_NoDup. }
      imp_steps. hret _; ss.
    }
    econs; ss.
    { kinit. harg. destruct x as [m n]. mDesAll. des; clarify.
      steps. unfold Add0.add, add_body. rewrite unfold_eval_imp. imp_steps.
      des_ifs.
      2: { exfalso. apply n. solve_NoDup. }
      unfold unint in *. des_ifs.
      hexploit FunStb_succ. i. inv H.
      imp_steps. rewrite FIND0. imp_steps. des.
      assert (exists m, z0 = Z.of_nat m).
      { exists (Z.to_nat z0). rewrite Z2Nat.id; auto. lia. } des. subst.
      hexploit GlobalStb_repeat; et. i. inv H. astart 1. acatch; et.
      hcall_weaken (Repeat1.repeat_spec FunStb sk) _ (_, _, _, Z.succ) _ with ""; et.
      { iPureIntro. splits; et. econs.
        { eapply SKWF. eauto. }
        econs.
        { et. }
        { etrans; [|et]. econs. ss. split.
          { ii. iIntros "H". iPure "H" as H. des. clarify.
            iModIntro. iSplits; et. }
          { ii. iIntros "H". iPure "H" as H. des; clarify. }
        }
      }
      { splits; ss. }
      mDesAll. des; clarify. imp_steps.
      guclo lordC_spec. econs.
      { instantiate (5:=100). eapply OrdArith.add_base_l. } (* TODO: make index reset tactics *)
      astop. steps. hret _; ss.
      iPureIntro. esplits; et.
      f_equal. f_equal. clear. generalize z. induction m; ss; i.
      { lia. }
      { rewrite <- IHm. lia. }
    }
    Unshelve. all:ss. all:try (exact 0).
  Qed.

End SIMMODSEM.
