Require Import Stack1 Client1 Mem1.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef Echo0 Echo1 SimModSem.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import TODOYJ.
Require Import HTactics Logic YPM.

Set Implicit Arguments.

Local Open Scope nat_scope.





Section AUX.
  Context `{Σ: GRA.t}.

  Context `{@GRA.inG Mem1.memRA Σ}.
  Lemma unfold_is_list: forall ll xs,
      is_list ll xs =
      match xs with
      | [] => (⌜ll = Vnullptr⌝: iProp)%I
      | xhd :: xtl =>
        (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl]))
                               ** is_list ltl xtl: iProp)%I
      end
  .
  Proof.
    i. destruct xs; auto.
  Qed.

  Lemma unfold_is_list_cons: forall ll xhd xtl,
      is_list ll (xhd :: xtl) =
      (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl]))
                             ** is_list ltl xtl: iProp)%I.
  Proof.
    i. eapply unfold_is_list.
  Qed.

  Context `{@GRA.inG Echo1.echoRA Σ}.

  Lemma echo_ra_merge
        ll0 ns0 ll1 ns1
    :
      (OwnM (echo_black ll0 ns0) -∗ OwnM (echo_white ll1 ns1) -∗ (⌜ll1 = ll0 /\ ns1 = ns0⌝))
  .
  Proof.
    iIntros "H0 H1". iCombine "H0" "H1" as "H0".
    iOwnWf "H0" as WF. iPureIntro.
    eapply Auth.auth_included in WF. des.
    eapply Excl.extends in WF; ss.
    - des; clarify.
    - ur; ss.
  Qed.

  Lemma echo_ra_white
        ll0 ns0 ll1 ns1
    :
      (OwnM (echo_white ll0 ns0) -∗ OwnM (echo_white ll1 ns1) -∗ ⌜False⌝)
  .
  Proof.
    iIntros "H0 H1". iCombine "H0" "H1" as "H0".
    iOwnWf "H0" as WF. iPureIntro.
    do 2 ur in WF. ss.
  Qed.

  Lemma echo_ra_black
        ll0 ns0 ll1 ns1
    :
      (OwnM (echo_black ll0 ns0) -∗ OwnM (echo_black ll1 ns1) -∗ ⌜False⌝)
  .
  Proof.
    iIntros "H0 H1". iCombine "H0" "H1" as "H0".
    iOwnWf "H0" as WF. iPureIntro.
    do 2 ur in WF. ss.
  Qed.
End AUX.
Global Opaque _APC.






Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.
  Context `{@GRA.inG Echo1.echoRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).
  Eval compute in (@URA.car Mem1._memRA).

  Let wf: W -> Prop :=
    @mk_wf
      _
      val
      (fun ll => ((∃ ns, (OwnM(echo_black ll ns)) ** is_list ll (List.map Vint ns)) ∨ (∃ ns, OwnM(echo_white ll ns)): iProp)%I)
      top2
      (fun ll mp_src mp_tgt => mp_tgt = ll↑)
  .
  Local Opaque is_list.

  Opaque points_to.

  Theorem correct: ModSemPair.sim Echo1.EchoSem Echo0.EchoSem.
  Proof.
    econstructor 1 with (wf:=wf); et; swap 2 3.
    { ss. econs; et. eapply to_semantic.
      { iIntros "H". iLeft. iExists _. iSplitL; ss.
        ss. rewrite unfold_is_list. iPureIntro. auto. }
      { eapply GRA.wf_embed. ur. split.
        { eexists (Excl.just (Vnullptr, [])). ur. auto. }
        { ur. ss. }
      }
    }

    econs; ss.
    { (* arg *)
      unfold echoF, echo_body, ccall. init. harg. destruct x.
      mDesAll. clarify. steps.
      mDesOr "INV"; cycle 1.
      { mAssertPure False; ss.
        iDestruct "INV" as (ns) "INV".
        iApply (echo_ra_white with "INV PRE"). }
      mDesAll. mAssertPure _.
      { iApply (echo_ra_merge with "INV PRE"). }
      des; subst.

      destruct (alist_find "getint" (StackStb ++ ClientStb ++ MemStb ++ EchoStb)) eqn:T; stb_tac; clarify.
      steps. rewrite Any.upcast_downcast in *. steps.
      hcall _ _ _ with "PRE"; et.
      mDesAll. clarify. steps.
      mDesOr "INV1".
      { mAssertPure False; ss. iDestruct "INV1" as (ns) "[INV1 _]".
        iApply (echo_ra_black with "INV INV1"). }
      mDesEx "INV1" as ns.
      mAssertPure _.
      { iApply (echo_ra_merge with "INV INV1"). }
      des; subst.
      rewrite Any.upcast_downcast in *. clarify.

      unfold unint in *. des_ifs; ss.
      { steps.
        destruct (alist_find "echo_finish" (StackStb ++ ClientStb ++ MemStb ++ EchoStb)) eqn:T; stb_tac; clarify.
        steps. rewrite Any.upcast_downcast. steps.
        hcall _ (_, _) _ with "*"; et.
        { iModIntro. iSplitR "INV1".
          { iLeft. iExists _. iFrame. }
          { iSplitL; ss. iSplitL; ss. }
        }
        { split; ss. }
        clarify. steps.

        hret _; ss.
        iModIntro. iSplitL; ss.
      }
      { des_sumbool. ss. }
      { steps. rewrite Any.upcast_downcast. steps. astart 1. acatch.

        hcall _ (_, _) _ with "- INV"; ss.
        { iModIntro. iSplitL "INV1"; ss.
          { iRight. iExists _. iFrame. }
          { iSplitL; ss. iExists _. iSplitL; ss. iSplitR "A"; ss. }
        }
        { split; ss. }
        steps. mDesAll. subst.
        eapply Any.upcast_inj in PURE0. des; clarify.
        rewrite Any.upcast_downcast in *. clarify.
        mDesOr "INV2".
        { mDesAll. mAssertPure False; ss.
          iApply (echo_ra_black with "INV INV2"). }
        mDesEx "INV2" as ns.
        mAssertPure _.
        { iApply (echo_ra_merge with "INV INV2"). }
        des; subst.

        mAssert _ with "INV INV2".
        { iCombine "INV" "INV2" as "INV". iApply (OwnM_Upd with "INV").
          instantiate (1:= echo_black v (z :: a0) ⋅ echo_white v (z :: a0)).
          eapply Auth.auth_update. rr. ii. des; ss. ur in FRAME. ur.
          destruct ctx2; ss; clarify. }
        mUpd "A". mDesOwn "A".

        astop. steps.
        destruct (alist_find "echo" (StackStb ++ ClientStb ++ MemStb ++ EchoStb)) eqn:T; stb_tac; clarify.
        steps. rewrite Any.upcast_downcast. steps.
        hcall _ (_, _) _ with "*"; ss.
        { iModIntro. iSplitR "A1"; ss.
          { iLeft. iExists _. iSplitL "A"; ss. }
          { iSplitL; ss. iSplitL; ss. }
        }
        { split; ss. }

        steps. hret _; ss.
        iFrame. iModIntro. ss.
      }
    }
    econs; ss.
    { (* arg *)
      unfold echo_finishF, echo_finish_body, ccall. init. harg. destruct x.
      mDesAll. clarify. steps.
      mDesOr "INV"; cycle 1.
      { mAssertPure False; ss. iDestruct "INV" as (ns) "INV".
        iApply (echo_ra_white with "INV PRE"). }
      mDesAll. mAssertPure _.
      { iApply (echo_ra_merge with "INV PRE"). }
      des; subst.

      rewrite Any.upcast_downcast. steps. destruct a0.
      { rewrite unfold_is_list in ACC. ss.
        mPure "A". subst. ss.
        steps. hret _; ss.
        iModIntro. iSplitL; ss. iRight. iExists _. iFrame.
      }
      rewrite unfold_is_list in ACC. ss. mDesAll. subst. ss.

      steps. astart 10. acatch. hcall _ 1 _ with "PRE"; ss.
      { iModIntro. iSplitL; ss.
        iRight. iExists _. iFrame. }
      { split; ss. }
      mDesSep "POST". mDesEx "POST". mDesSep "POST".
      mPure "A". mPure "POST". clarify.
      eapply Any.upcast_inj in PURE0.
      rewrite Any.upcast_downcast. steps. des; clarify.

      acatch. hcall _ (_, _) _ with "- INV"; ss.
      { iModIntro. iSplitL "INV1"; ss. iSplitL; ss.
        iExists _. iSplitL; ss. iSplitR "A3"; ss.
        { iSplit; ss. instantiate (1:=Vint z :: (map Vint a0)). clear.
          rewrite unfold_is_list_cons. iExists _, _. iFrame; ss.
        }
        { iExists _. et. }
      }
      { split; ss. }
      ss. steps. mDesSep "POST". mDesEx "POST". mDesSep "POST".
      mDesSep "POST". mPure "A". mPure "POST". subst.
      eapply Any.upcast_inj in PURE0. erewrite Any.upcast_downcast in *.
      des; clarify. mDesOr "INV2".
      { mAssertPure False; ss.
        iDestruct "INV2" as (ns) "[INV2 _]".
        iApply (echo_ra_black with "INV2 INV"). }

      mAssert _ with "INV INV2".
      { iDestruct "INV2" as (ns) "INV2". iCombine "INV" "INV2" as "INV".
        iApply (OwnM_Upd with "INV").
        instantiate (1:= echo_black v (z :: a0) ⋅ echo_white v (z :: a0)).
        eapply Auth.auth_update. rr. ii. des; ss. ur in FRAME. ur.
        destruct ctx2; ss; clarify. }
      mUpd "A". mDesOwn "A".

      acatch. hcall _ (_, _, _) _ with "A1 A3"; ss.
      { iModIntro. iSplitL "A3".
        { iRight. iExists _. iFrame. }
        { iSplit; ss. iSplit; ss. iSplit; ss. }
      }
      { splits; ss. }
      steps. astop. steps.
      destruct (alist_find "putint" (StackStb ++ ClientStb ++ MemStb ++ EchoStb)) eqn:T; stb_tac; clarify.
      mDesSep "POST". mDesSep "POST". mPure "A1". mPure "A3".
      steps. eapply Any.upcast_inj in PURE0. des; clarify.
      rewrite Any.upcast_downcast in *. clarify. steps.

      hcall _ _ _ with "INV"; ss.
      { iModIntro. iSplit; ss. }
      { split; ss. }
      mDesAll. mDesOr "INV1".
      { mAssertPure False; ss.
        iDestruct "INV1" as (ns) "[INV1 _]".
        iApply (echo_ra_black with "INV1 A"). }
      mDesAll. mAssertPure _.
      { iApply (echo_ra_merge with "A INV1"). }
      des; subst. steps.

      destruct (alist_find "echo_finish" (StackStb ++ ClientStb ++ MemStb ++ EchoStb)) eqn:T; stb_tac; clarify.
      steps. rewrite Any.upcast_downcast. steps.
      hcall _ (_, _) _ with "A A2 INV1"; ss.
      { iCombine "A" "INV1" as "A".
        iPoseProof (OwnM_Upd with "A") as "A".
        { instantiate (1:= echo_black _ _ ⋅ echo_white _ _).
          eapply Auth.auth_update. rr. ii. des; ss. ur in FRAME. ur.
          destruct ctx4; ss; clarify. }
        iMod "A". iDestruct "A" as "[A0 A1]". iModIntro.
        iSplitR "A1".
        { iLeft. iExists _. iSplitL "A0"; ss. }
        { iSplit; ss. iSplit; ss. }
      }
      { split; ss. }

      steps. hret _; ss.
      { iSplitL "INV"; ss. }
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
