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

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.






Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG knotRA Σ}.

  Let W: Type := (Σ * Any.t) * (Σ * Any.t).

  Variable RecStb: SkEnv.t -> list (gname * fspec).
  Variable FunStb: SkEnv.t -> list (gname * fspec).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = (ε, tt↑)>>) /\
      (<<TGT: mrps_tgt0 = (ε, tt↑)>>)
  .

  Variable RecStb_incl
    :
      forall skenv fn fsp
             (SPECS: List.find (fun '(_fn, _) => dec fn _fn) (RecStb skenv) = Some fsp),
        List.find (fun '(_fn, _) => dec fn _fn) (GlobalStb skenv) = Some fsp.

  Variable FunStb_incl
    :
      forall skenv fn fsp
             (SPECS: List.find (fun '(_fn, _) => dec fn _fn) (MainFunStb RecStb skenv) = Some fsp),
        List.find (fun '(_fn, _) => dec fn _fn) (FunStb skenv) = Some fsp.

  Hypotheses GlobalStb_knot
    :
      forall skenv,
        List.find (fun '(_fn, _) => dec "knot" _fn) (GlobalStb skenv) = Some ("knot", knot_spec RecStb FunStb skenv).

  Theorem correct: ModPair.sim (KnotMain1.Main RecStb GlobalStb) KnotMain0.Main.
  Proof.
    econs; ss; [|admit ""].
    i. eapply adequacy_lift.
    econstructor 1 with (wf:=wf); et; ss.
    econs; ss; [|econs; ss].
    { init. unfold fibF, ccall. harg_tac.
      destruct x as [x INV]. ss. des. subst.
      iRefresh. iDestruct PRE. iPure PRE. des; clarify.
      eapply Any.upcast_inj in PRE. des; clarify. steps.
      rewrite Any.upcast_downcast in _UNWRAPN. clarify. astart 2. steps.
      rewrite PRE1. ss. steps.
      des_ifs.
      { astop. steps. force_l. eexists.
        hret_tac (@URA.unit Σ) A; ss. esplits; eauto.
        iRefresh. iSplitR A; ss. red. red. f_equal. f_equal.
        clear - l. destruct x; ss. destruct x; ss. lia.
      }
      steps.
      acall_tac_weaken (mrec_spec INV) (x - 1) (ord_pure (2 * x - 1)) (@URA.unit Σ) (@URA.unit Σ) A; ss.
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
      acall_tac_weaken (mrec_spec INV) (x - 2) (ord_pure (2 * (x - 1) - 1)) (@URA.unit Σ) (@URA.unit Σ) A; ss.
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
      hret_tac (@URA.unit Σ) A; ss.
      splits; ss. iRefresh. iSplitR A; ss. red. red.
      repeat f_equal. destruct x; ss. destruct x; ss.
      clear - g.
      remember (match x with
                | 0 => 1
                | S n'' => Fib x + Fib n''
                end). clear Heqn. rewrite Nat.sub_0_r. lia.
    }
    { init. unfold mainF, ccall. harg_tac. des; clarify.
      iRefresh. iDestruct PRE. iPure A. des; clarify.
      rewrite Any.upcast_downcast. ss. steps.
      hexploit (SKINCL "fib"); ss; eauto. i. des.
      rewrite H0. ss. steps.
      astart 2.
      acall_tac Fib (ord_pure 0) (@URA.unit Σ) (@URA.unit Σ) PRE; ss.
      { eapply GlobalStb_knot. }
      { splits; ss. iRefresh. iSplitR PRE; ss.
        { red. red. esplits; eauto.
          { eapply SKWF. eauto. }
          { eapply FunStb_incl. des_ifs. }
          { ii. ss. eexists (x_src, Own (GRA.embed (knot_frag (Some Fib)))). splits; ss.
            { i. iRefresh. iIntro. des. split; auto. iRefresh.
              iDestruct A. iPure A. des; clarify. iSplitR A1; ss.
              red. red. esplits; eauto.
              { ii. ss. exists (Fib, x_src0). splits; ss.
                { i. iRefresh. iIntro. des. split; auto. iRefresh.
                  iDestruct A0. iPure A0. des; clarify.
                  iSplitL A4; ss.
                }
                { i. iRefresh. iIntro. des. split; auto. iRefresh.
                  iDestruct A0. iPure A4. iSplitR A0; ss. }
              }
            }
            { i. iRefresh. iIntro. des. split; auto. iRefresh.
              iDestruct A. iPure A. iSplitR A1; ss.
            }
          }
        }
        { exists None. iRefresh. ss. }
      }
      ss. des. clarify. iRefresh. iDestruct POST. iPure POST. des; clarify.
      eapply Any.upcast_inj in POST. des; clarify.
      steps. rewrite Any.upcast_downcast in _UNWRAPN. clarify.
      ss. steps. rewrite POST0. steps.
      acall_tac (Fib, 10) (ord_pure 21) (@URA.unit Σ) (@URA.unit Σ) A; ss.
      { eapply RecStb_incl. eauto. }
      { splits; ss. iRefresh. iSplitL A; ss. }
      steps. ss. des. clarify.
      iRefresh. iDestruct POST. iPure A.
      erewrite Any.upcast_downcast in _UNWRAPN. clarify.
      eapply Any.upcast_inj in A. des; clarify.
      astop. steps.
      hret_tac (@URA.unit Σ) (@URA.unit Σ); ss.
    }
  Qed.

End SIMMODSEM.
