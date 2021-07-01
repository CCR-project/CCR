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

Require Import HTactics ProofMode Invariant TODOYJ.
Require Import STB.

Local Open Scope nat_scope.






Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Let W: Type := Any.t * Any.t.

  Variable RecStb: SkEnv.t -> gname -> option fspec.
  Variable FunStb: SkEnv.t -> gname -> option fspec.
  Variable GlobalStb: SkEnv.t -> gname -> option fspec.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _ unit
      (fun _ _ _=> True%I)
  .

  Hypothesis RecStb_incl: forall skenv,
      stb_incl (RecStb skenv) (GlobalStb skenv).

  Hypothesis FunStb_fib: forall skenv,
      fn_has_spec (FunStb skenv) "fib" (fib_spec RecStb skenv).

  Hypotheses GlobalStb_knot: forall skenv,
      fn_has_spec (GlobalStb skenv) "knot" (knot_spec RecStb FunStb skenv).

  Theorem correct: ModPair.sim (KnotMain1.Main RecStb GlobalStb) KnotMain0.Main.
  Proof.
    econs; ss. i. econstructor 1 with (wf:=wf) (le:=top2); ss; et.
    2: { eexists. econs; ss. red. uipropall. }
    eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF.
    econs; ss; [|econs; ss].
    { init. unfold fibF, ccallU. harg.
      destruct x as [x INV]. mDesAll. ss. des. subst.
      rewrite Any.upcast_downcast. steps.
      inv PURE3. rewrite FBLOCK. ss. steps.
      des_ifs.
      { astart 0. astop. steps. force_l. eexists. steps.
        hret _; ss. iModIntro. iFrame; ss. iPureIntro.
        esplits; eauto. f_equal. f_equal.
        clear - l. destruct x; ss. destruct x; ss. lia.
      }
      steps. inv SPEC. astart 10. acatch.
      { eapply RecStb_incl. eauto. }

      hcall_weaken _ _ _ _ with "A"; et.
      { ss. iModIntro. iFrame; ss. iSplitR; ss.
        iPureIntro. splits; et. instantiate (1:=(x - 1%nat)).
        repeat f_equal. lia.
      }
      { splits; ss. eauto with ord_step. }
      steps. ss. mDesAll. clarify.
      erewrite Any.upcast_downcast in *. clarify. steps. acatch.
      { eapply RecStb_incl. eauto. }
      hcall_weaken _ _ _ _ with "A"; et.
      { ss. iModIntro. iFrame; ss.
        iSplitR; ss. iSplitR; ss.
        iPureIntro. instantiate (1:=(x - 2%nat)).
        repeat f_equal. lia.
      }
      { splits; ss. eauto with ord_step. }
      steps. ss. mDesAll. clarify.
      erewrite Any.upcast_downcast in *. clarify. steps.

      astop. force_l. eexists. steps. hret _; ss.
      { ss. iModIntro. iFrame; ss. iSplitR; ss.
        iPureIntro. repeat f_equal. ss. destruct x; ss. destruct x; ss.
        remember (match x with
                  | 0 => 1
                  | S n'' => Fib x + Fib n''
                  end). clear Heqn. rewrite Nat.sub_0_r. lia. }
    }
    { init. unfold mainF, ccallN, ccallU. harg. mDesAll. subst.
      steps. astart 2.
      hexploit (SKINCL "fib"); ss; eauto. i. des.
      rewrite FIND. ss. steps.
      specialize (GlobalStb_knot sk). inv GlobalStb_knot.
      acatch; eauto.
      hcall_weaken _ _ _ _ with "*"; et.
      { ss. iModIntro. iFrame; ss.
        iSplitL; ss. iSplitR; ss.
        { iPureIntro. esplits; eauto. econs.
          { eapply SKWF. eauto. }
          eapply fn_has_spec_weaker; eauto. ii. ss.
          eexists (x_src, OwnM (knot_frag (Some Fib)) ** inv_closed).
          splits; ss.
          { i. iIntros "[CLOSED [[% H] %]]".
            iModIntro. iFrame; ss.
            iPureIntro. des. esplits; et.
            eapply fb_has_spec_weaker; eauto.
            ii. ss. exists (Fib, x_src0). splits; ss.
            { i. iIntros "[[% [H0 H1]] %]".
              iModIntro. iFrame; ss. }
            { i. iIntros "[CLOSED [[% H] %]]".
              iModIntro. iFrame; ss. }
          }
          { i. iIntros "[[% [H0 H1]] %]".
            iModIntro. iFrame; ss. }
        }
        { iExists _. iExact "A1". }
      }
      { splits; ss. }
      mDesAll. des; clarify. rewrite Any.upcast_downcast. steps.
      inv PURE3. rewrite FBLOCK. inv SPEC. steps. acatch.
      { eapply RecStb_incl. eauto. }
      hcall_weaken _ _ _ _ with "*"; et.
      { ss. iModIntro. instantiate (2:=(_, 10)). ss. iFrame; ss. }
      { split; ss. }
      mDesAll. subst. rewrite Any.upcast_downcast. steps.
      astop. steps. hret _; ss.
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
