Require Import HoareDef KnotHeader KnotMain0 KnotMain1 Knot1 SimModSemL SimModSem.
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
Require Import STB.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.






Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).

  Variable RecStb: SkEnv.t -> list (gname * fspec).
  Variable FunStb: SkEnv.t -> list (gname * fspec).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists mr,
        (<<SRC: mrps_src0 = (mr, tt↑)>>) /\
        (<<TGT: mrps_tgt0 = (ε, tt↑)>>)
  .

  Hypothesis RecStb_incl: forall skenv,
      stb_incl (RecStb skenv) (GlobalStb skenv).

  Hypothesis FunStb_fib: forall skenv,
      fn_has_spec (FunStb skenv) "fib" (fib_spec RecStb skenv).

  Hypotheses GlobalStb_knot: forall skenv,
      fn_has_spec (GlobalStb skenv) "knot" (knot_spec RecStb FunStb skenv).

  Theorem correct: ModPair.sim (KnotMain1.Main RecStb GlobalStb) KnotMain0.Main.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf); ss; et.
    econs; ss; [|econs; ss].
    { init. unfold fibF, ccall. harg_tac.
      destruct x as [x INV]. ss. des. subst.
      iRefresh. iDestruct PRE. iPure PRE. des; clarify.
      eapply Any.upcast_inj in PRE. des; clarify. steps.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify. astart 2. steps.
      inv PRE1. rewrite FBLOCK. ss. steps.
      des_ifs.
      { astop. steps. force_l. eexists.
        hret_tac (@URA.unit Σ) A; ss; et. esplits; eauto.
        iRefresh. iSplitR A; ss. red. red. f_equal. f_equal.
        clear - l. destruct x; ss. destruct x; ss. lia.
      }
      steps. inv SPEC.
      acall_tac_weaken (mrec_spec Fib INV) (x - 1) (ord_pure (2 * x - 1)) (@URA.unit Σ) (@URA.unit Σ) A; ss; et.
      { eapply RecStb_incl. eauto. }
      { ss. splits; ss. iRefresh. iSplitR A; ss.
        red. red. esplits; eauto.
        { repeat f_equal. clear - g. lia. }
        { f_equal. clear - g. eauto with ord_step. }
      }
      { esplits; ss. eauto with ord_step. }
      steps. ss. des. clarify. iRefresh. iDestruct POST. iPure POST.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify.
      eapply Any.upcast_inj in POST. des; clarify. steps.
      acall_tac_weaken (mrec_spec Fib INV) (x - 2) (ord_pure (2 * (x - 1) - 1)) (@URA.unit Σ) (@URA.unit Σ) A; ss; et.
      { eapply RecStb_incl. eauto. }
      { splits; ss. iRefresh. iSplitR A; ss.
        red. red. esplits; eauto.
        { repeat f_equal. clear - g. lia. }
        { f_equal. clear - g. eauto with ord_step. }
      }
      { esplits; ss. eauto with ord_step. }
      steps. ss. des. clarify. iRefresh. iDestruct POST. iPure POST.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify.
      eapply Any.upcast_inj in POST. des; clarify. steps.
      astop. force_l. eexists.
      hret_tac (@URA.unit Σ) A; ss; et.
      splits; ss. iRefresh. iSplitR A; ss. red. red.
      repeat f_equal. destruct x; ss. destruct x; ss.
      clear - g.
      remember (match x with
                | 0 => 1
                | S n'' => Fib x + Fib n''
                end). clear Heqn. rewrite Nat.sub_0_r. lia.
    }
    { init. unfold mainF, ccall. harg_tac. des; clarify.
      iRefresh. iDestruct PRE. iDestruct PRE. iPure PRE. des; clarify.
      rewrite Any.upcast_downcast. ss. steps.
      hexploit (SKINCL "fib"); ss; eauto. i. des.
      rewrite FIND. ss. steps.
      astart 2. specialize (GlobalStb_knot sk). inv GlobalStb_knot.
      acatch; eauto. iMerge A0 A.
      hcall_tac_weaken (knot_spec2 RecStb FunStb sk) Fib (ord_pure 1) (@URA.unit Σ) (@URA.unit Σ) A0; ss; et.
      { etrans; eauto. eapply knot_spec2_weaker. }
      { splits; ss. iRefresh.
        iDestruct A0. iSplitR A; ss. iSplitR A0; ss.
        red. red. esplits; eauto. econs.
        { eapply SKWF. eauto. }
        eapply fn_has_spec_weaker; eauto.
        ii. ss.
        eexists (x_src, Own (GRA.embed (knot_frag (Some Fib))) ** inv_closed).
        splits; ss.
        { i. iRefresh. iIntro. des. split; auto. iRefresh.
          iDestruct A. iDestruct A. iMerge A0 A1. iSplitR A0; ss.
          iPure A. des; clarify.
          red. red. esplits; eauto. eapply fb_has_spec_weaker; eauto.
          ii. ss. exists (Fib, x_src0). splits; ss.
          { i. iRefresh. iIntros. des. split; auto. iRefresh.
            iDestruct A0. iDestruct A3. iSplitR A2; ss. iSplitR A3; ss. }
          { i. iRefresh. iIntro. des. split; auto. iRefresh.
            iDestruct A0. iDestruct A0. iMerge A2 A3. iSplitR A2; ss. }
        }
        { i. iRefresh. iIntros. des. split; auto. iRefresh.
          iDestruct A. iDestruct A1. iSplitR A0; ss. iSplitR A1; ss. }
      }
      ss. des. clarify. iRefresh. iDestruct POST. iDestruct POST.
      iPure POST. des; clarify.
      eapply Any.upcast_inj in POST. des; clarify.
      steps. rewrite Any.upcast_downcast in _UNWRAPN. clarify.
      ss. steps. inv POST0. rewrite FBLOCK. inv SPEC. steps. acatch.
      { eapply RecStb_incl. eauto. }
      hcall_tac_weaken (mrec_spec Fib x0) 10 (ord_pure 21) (@URA.unit Σ) (@URA.unit Σ) A; ss; et.
      { splits; ss. iRefresh. iSplitR A; ss. }
      steps. ss. des. clarify.
      iRefresh. iDestruct POST. iPure POST.
      erewrite Any.upcast_downcast in _UNWRAPN. clarify.
      eapply Any.upcast_inj in POST. des; clarify.
      astop. steps.
      hret_tac (@URA.unit Σ) (@URA.unit Σ); ss; et.
    }
  Qed.

End SIMMODSEM.
