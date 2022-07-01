Require Import HoareDef MapHeader MapM MapA SimModSem.
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

Require Import HTactics2 ProofMode STB Invariant.
Require Import Mem1.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.
  Context `{Σ: GRA.t}.

  Context `{@GRA.inG MapRA0 Σ}.
  Context `{@GRA.inG MapRA1 Σ}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := Any.t * Any.t.

  Definition initial_map: iProp :=
    OwnM (Excl.unit, Auth.excl ((fun _ => Excl.just 0%Z): @URA.car (nat ==> (Excl.t Z))%ra) ((fun _ => Excl.just 0%Z): @URA.car (nat ==> (Excl.t Z))%ra)).

  Definition black_map (f: Z -> Z): iProp :=
    OwnM (Excl.unit, Auth.black ((fun k => Excl.just (f k)): @URA.car (nat ==> (Excl.t Z))%ra)).

  Definition unallocated (sz: Z): iProp :=
    OwnM (Excl.unit, Auth.white ((fun k =>
                                    if (Z_gt_le_dec 0 k) then Excl.just 0%Z
                                    else if (Z_gt_le_dec sz k) then Excl.unit else Excl.just 0%Z)
                                  : @URA.car (nat ==> (Excl.t Z))%ra)).

  Lemma initial_map_initialize sz
    :
    initial_map -∗ #=> (black_map (fun _ => 0%Z) ** initial_points_tos sz ** unallocated sz).
  Proof.
  Admitted.

  Lemma initial_map_no_points_to k v
    :
    initial_map -∗ map_points_to k v -∗ ⌜False⌝.
  Proof.
  Admitted.

  Lemma unallocated_range sz k v
    :
    unallocated sz -∗ map_points_to k v -∗ ⌜(0 <= k < sz)%Z⌝.
  Proof.
  Admitted.

  Lemma black_map_get f k v
    :
    black_map f -∗ map_points_to k v -∗ (black_map f ** map_points_to k v ** (⌜f k = v⌝)).
  Proof.
  Admitted.

  Lemma black_map_set f k w v
    :
    black_map f -∗ map_points_to k w -∗ #=> (black_map (fun n => if Z.eq_dec n k then v else f n) ** map_points_to k v).
  Proof.
  Admitted.

  Let wf: _ -> W -> Prop :=
        @mk_wf
          _ unit
          (fun _ st_src st_tgt =>
             ((∃ f sz, ⌜st_src = f↑ /\ st_tgt = (f, sz)↑⌝ ** black_map f ** unallocated sz ** pending1) ∨ (initial_map))%I).

  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Hypothesis STB_set: forall sk, (GlobalStb sk) "set" = Some set_spec.

  Hypothesis PUREINCL: forall sk, stb_pure_incl (GlobalStbM sk) (GlobalStb sk).

  Lemma pending1_unique:
    pending1 -∗ pending1 -∗ False%I.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". exfalso. clear - H2.
    rr in H2. ur in H2. unseal "ra". des.
    rr in H2. ur in H2. unseal "ra". ss.
  Qed.

  Theorem correct: refines2 [MapM.Map GlobalStbM] [MapA.Map GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits. econs; et. eapply to_semantic. iIntros "H". iSplitL "H"; eauto. iApply Own_unit. ss. }
    Local Opaque black_map map_points_to unallocated.
    econs.
    { admit "". }

    econs; ss.

    {
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** get ***)
      unfold MapM.getF, MapA.getF, ccallU, ccallN.
      harg. fold wf. destruct x. ss.
      mDesAll; des; clarify.
      mDesOr "INVS".
      2:{ mAssertPure False; ss. iApply (initial_map_no_points_to with "INVS A1"). }
      mDesAll. des; subst.
      mAssertPure (0 ≤ n < a0)%Z.
      { iApply (unallocated_range with "A2 A1"); eauto. }
      harg_tgt.
      { iModIntro. iFrame. iSplits; et. xtra. }
      steps. force_r; auto. steps.
      (*** calling APC ***)
      hAPC _; try assumption.
      { iIntros "A"; iDes. iSplitR "A2".
        { iLeft. iExists _, _. iFrame. iSplits; auto. }
        { iApply "A2". }
      }
      { auto. }
      fold wf. steps. s


astop.

r in WLE. des_ifs. astart 1. astep "Map.new" (([]: list val)↑). stb_tac. clarify.




    {
      (*** init ***)
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)

      unfold MapM.initF, MapA.initF, ccallU, ccallN.

      harg. fold wf.
      mDesAll; des; clarify.
      mDesOr "INVS".
      { mDesAll. des; subst. mAssertPure False; ss.
        unfold pending. iDestruct "A1" as "[H0 H1]".
        iApply (pending1_unique with "A H1").
      }
      unfold pending in ACC. mDesAll. steps.
      harg_tgt.
      { iModIntro. iFrame. iSplits; et. xtra. }
      steps.
      (*** calling APC ***)
      hAPC _; try assumption.
      { iIntros "A"; iDes. iSplitL "A".
        - iRight. iLeft. iSplits; et.
        - xtra.
      }
      fold wf. steps. r in WLE. des_ifs. astart 1. astep "Map.new" (([]: list val)↑). stb_tac. clarify.


        (*** calling Map.new ***)
        hcall _ _.
        {
          iDes; ss; des; clarify.
          { iExFalso. iApply (mw_stateX_false with "INIT"); et. }
          iModIntro. iSplits; ss. iSplitL "A".
          { xtra. }
          { iRight. iRight. iSplits; ss; et. iFrame. }
        }
        { esplits; ss; et. }
        fold wf. steps. astop. steps. mDesAll; des; clarify. r in WLE0. des_ifs.
        force_l; stb_tac; ss; clarify. steps.

        hpost_tgt.
        { iModIntro. iFrame. iSplits; ss.
          iAssert ({{"LOCKED": ∃ f : Z → option Z,
                 ((OwnM (mw_state f) ** OwnM (mw_stateX f)) ** ⌜mp_src0 = Any.upcast f⌝) **
                 ⌜Some (Any.upcast (λ _ : Z, None), Any.upcast tt) = Some (mp_src0, mp_tgt0)⌝}})%I
            with "[INV]" as "INV".
          { iDes; ss. iSplits; ss; et. iFrame. }
          xtra.
        }
        fold wf. steps. stb_tac; ss; clarify. steps. hide_k.



        (*** calling App.init ***)
        hcall _ _.
        { iDes; ss; des; clarify. apply Any.upcast_inj in H10. des; clarify. clear_fast.
          iModIntro. iSplits; ss; et.
          iSplitR "LOCKED A A0"; cycle 1.
          { iFrame. iSplits; ss; et. }
          iSplitR.
          { instantiate (1:=True%I); ss. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { i. iIntros "H". ss. iDes; des; clarify. }
        unhide_k. steps. fold wf. mDesAll. des; clarify.



        hpost_tgt.
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. xtra. }
        fold wf. steps. force_l; stb_tac; ss; clarify. steps.
        stb_tac; clarify.



        (*** calling loop ***)
        Opaque Z.eq_dec.
        hcall _ _.
        { iDes; ss; des; clarify; cycle 1.
          { iExFalso. iApply (mw_state_false with "A2"); et. }
          iModIntro. iSplits; ss; et. iSplitR "A A0 FR"; cycle 1.
          { iSplits; ss; et. iFrame. iSplits; ss; et. }
          iSplitR.
          { instantiate (1:=True%I); ss. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { i. iIntros "H". ss. iDes. des; clarify. }
        steps. fold wf. mDesAll. des; clarify.

        hpost_tgt.
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. xtra. }
        steps. fold wf.


        (*** returning ***)
        hret None; ss.
        { iModIntro. iDes; ss; clarify; cycle 1.
          { iExFalso. iApply (mw_state_false with "A"); et. }
          iFrame.
          iSplitL; cycle 1.
          { iSplits; ss; et. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { iDes. clarify. iPureIntro. clarify. r. fold wf in WF0. exists None; esplits; et. }
      }
      { (* LOCKED *) mAssertPure False; ss. iApply (mw_stateX_false with "A1"); et. }
    }



    econs.
    {
      (*** init ***)
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)

      unfold loopF, MWC2.loopF, ccallU, ccallN.

      harg. fold wf. mDesAll; des; clarify.
      mDesOr "INVS"; mDesAll; des; clarify; steps.
      { (* INIT *)
        force_l; stb_tac; ss; clarify. steps.
        harg_tgt.
        { iModIntro. iFrame. iSplits; et. xtra. }
        steps. stb_tac; ss; clarify.

        hcall _ _.
        { iDes. iModIntro. iFrame. iSplits; ss; et. iSplitR.
          { instantiate (1:=True%I); ss. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { i. iIntros "H". ss. iDes; des; clarify. }
        fold wf. steps. mDesAll; des; clarify. force_l; stb_tac; ss; clarify. steps.


        hpost_tgt.
        { iModIntro. iFrame. iSplits; ss; et. xtra. }
        fold wf. steps. stb_tac; ss; clarify.


        hcall _ _.
        { iDes; ss; cycle 1.
          { iExFalso. iApply (mw_state_false with "A2"); et. }
          iModIntro. iFrame. iSplits; ss; et. iSplitR.
          { instantiate (1:=True%I); ss. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { i. iIntros "H". ss. iDes. des; clarify. }
        fold wf. steps. mDesAll; des; clarify. rewrite Any.upcast_downcast in *. clarify.

        hpost_tgt.
        { iModIntro. iFrame. iSplits ;ss; et. xtra. }
        fold wf. steps.


        hret None; ss.
        { iDes; ss; clarify; cycle 1.
          { iExFalso. iApply (mw_state_false with "A"); et. }
          iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame.
        }
        { iDes. clarify. iPureIntro. clarify. r. fold wf in WF0. exists None; esplits; et. }
      }
      mDesOr "INVS"; mDesAll; des; clarify; steps.
      { (* UNINIT *) mAssertPure False; ss. iApply (mw_state_false with "A1"); et. }
      { (* LOCKED *) mAssertPure False; ss. iApply (mw_state_false with "A1"); et. }
    }


    econs.
    {
      (*** init ***)
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)

      unfold putF, MWC2.putF, ccallU, ccallN.

      harg. fold wf. mDesAll; ss; des; clarify. des_ifs_safe; ss. mDesAll; des; ss; clarify.
      mDesOr "INVS".
      { (* INIT *)
        mDesAll; des; clarify.
        mAssertPure (o = a).
        { iApply (mw_state_eq with "A1"). iFrame. }
        subst. rename a into full.
        steps.
        rename a2 into lst0. rename z0 into k. rename z into v.
        change (λ k1 : Z, if dec k k1 then Some v else full k1) with (add k v full).
        harg_tgt.
        { iPoseProof ((mw_state_upd _ _ (add k v full)) with "A1 INIT") as "B".
          iMod "B". iModIntro. iFrame. iSplits; ss; et. xtra. }
        fold wf. steps. force_r; ss. steps.
        destruct (dec (lst_cls lst0 k) uninit).
        - steps.
          unfold set. destruct (dec k k); ss. destruct x; steps.
          + hAPC _; ss.
            { iIntros "H"; iDes. iSplitL "A A0".
              - iRight. iRight. iSplits; et. iFrame.
              - iAssumption.
            }
            steps. fold wf. r in WLE. des_ifs. rewrite _UNWRAPU. steps.


            hret None; ss.
            { iDes; ss; clarify. apply Any.upcast_inj in H6. des; clarify.
              iModIntro. iFrame. iSplits; ss; et. iLeft. iSplits; ss; et.
              { iFrame. iAssumption. }
              clear - PURE. iPureIntro. r. r in PURE. ss. i. specialize (PURE k0 v0). des_ifs; et.
            }
            { iDes; des; clarify. iPureIntro. r. fold wf in WF0. exists None; esplits; et. }
          + steps.
            astart 1. astep "Map.update" ([lst_map lst0; Vint k; Vint v]↑). stb_tac; ss; clarify.
            hcall _ (Some (_, _)).
            { iDes; clarify. instantiate (2:=(_, _, _, _)). cbn. iModIntro. iSplits; ss; et. iFrame.
              iSplitL.
              - iSplitR. { instantiate (1:=True%I); ss. } iRight. iRight. iSplits; ss; et. iSplitL "A"; ss.
              - instantiate (1:=k). iSplits; ss; et. rewrite PURE2; ss.
            }
            { i. iIntros "H". ss. }
            fold wf. mDesAll; des; clarify. steps. astop. steps.

            hpost_tgt.
            { iModIntro. iFrame. iSplits; ss. xtra. }
            steps. fold wf. ss. des_ifs. rewrite _UNWRAPU. steps.
            hret None; ss.
            { iDes; ss; clarify. iModIntro. iSplits; ss; et. apply Any.upcast_inj in H6. des; clarify.
              iSplitR "A A1"; ss; et.
              - iLeft. iSplits; ss; et; iFrame.
                clear - PURE. iPureIntro. r. r in PURE. ss. i. specialize (PURE k0 v0). des_ifs; et.
              - iFrame. iSplits; ss; et.
            }
            { iDes; des; clarify. iPureIntro. r. fold wf in WF0. exists None; esplits; et. }
        - steps.
          destruct (lst_cls lst0 k) eqn:T; ss.
          + steps. hAPC _; ss.
            { iIntros "H"; iDes. iSplitL "A A0".
              - iRight. iRight. iSplits; et. iFrame.
              - iAssumption.
            }
            steps. fold wf. r in WLE. des_ifs. rewrite _UNWRAPU. steps.


            hret None; ss.
            { iDes; ss; clarify. apply Any.upcast_inj in H6. des; clarify.
              iModIntro. iFrame. iSplits; ss; et. iLeft. iSplits; ss; et.
              { iFrame. iAssumption. }
              clear - T PURE. iPureIntro. r. r in PURE. ss. i. specialize (PURE k0 v0). unfold set.
              des_ifs; et; try congruence.
            }
            { iDes; des; clarify. iPureIntro. r. fold wf in WF0. exists None; esplits; et. }
          + steps.
            astart 1. astep "Map.update" ([lst_map lst0; Vint k; Vint v]↑). stb_tac; ss; clarify.
            hcall _ (Some (_, _)).
            { iDes; clarify. instantiate (2:=(_, _, _, _)). cbn. iModIntro. iSplits; ss; et. iFrame.
              iSplitL.
              - iSplitR. { instantiate (1:=True%I); ss. } iRight. iRight. iSplits; ss; et. iSplitL "A"; ss.
              - instantiate (1:=k). iSplits; ss; et. rewrite PURE2; ss.
            }
            { i. iIntros "H". ss. }
            fold wf. mDesAll; des; clarify. steps. astop. steps.

            hpost_tgt.
            { iModIntro. iFrame. iSplits; ss. iCombine "A1" "INV" as "A". iAssumption. }
            steps. fold wf. ss. des_ifs. rewrite _UNWRAPU. steps.
            hret None; ss.
            { iDes; ss; clarify. iModIntro. iSplits; ss; et. apply Any.upcast_inj in H6. des; clarify.
              iSplitR "A A1"; ss; et.
              - iLeft. iSplits; ss; et; iFrame.
                clear - T PURE. iPureIntro. r. r in PURE. ss. i. specialize (PURE k0 v0).
                des_ifs; et; try congruence.
              - iFrame. iSplits; ss; et.
            }
            { iDes; des; clarify. iPureIntro. r. fold wf in WF0. exists None; esplits; et. }
      }
      mDesOr "INVS"; mDesAll; des; clarify.
      { (* UNINIT *) mAssertPure False; ss. iApply (mw_state_false with "A1"); et. }
      { (* LOCKED *) mAssertPure False; ss. iApply (mw_state_false with "A1"); et. }
    }

    econs.
    {
      (*** init ***)
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)

      unfold getF, MWC2.getF, ccallU, ccallN.

      harg. fold wf. mDesAll; ss; des; clarify. des_ifs_safe; ss. mDesAll; des; ss; clarify.
      mDesOr "INVS".
      { (* INIT *)
        mDesAll; des; clarify.
        mAssertPure (o = a).
        { iApply (mw_state_eq with "A1"). iFrame. }
        subst. rename a into full.
        steps.
        rename a2 into lst0. rename z0 into k. rename z into v.
        rewrite PURE1. steps.

        harg_tgt.
        { iModIntro. iFrame. iSplits; ss; et. xtra. }
        steps. fold wf. force_r; ss. steps. force_r.
        { exploit PURE; et. i. des_ifs. }
        steps.
        des_ifs.
        - steps. hAPC (Some (_, _)); ss.
          { iIntros "[A [B C]]". iSplitR "A"; try iAssumption. iRight. iRight. iSplits; ss; et. iFrame. }
          fold wf. steps.
          assert(T: lst_opt lst0 k = (Vint v)).
          { r in PURE. exploit PURE; et. i; des_ifs. }
          rewrite T. steps. rewrite _UNWRAPU. steps.
          hret None; ss.
          { iDes; ss; clarify. iModIntro. apply Any.upcast_inj in H6. des; clarify. iFrame. iSplits; ss; et.
            iLeft. iSplits; ss; et. { iFrame. } }
          { iDes; des; clarify. iPureIntro. r. fold wf in WF0. exists None; esplits; et. }
        - steps. astart 1. astep "Map.access" ([lst_map lst0; Vint k]↑). stb_tac; ss; clarify.
          hcall _ (Some (_, _)).
          { iDes; clarify. instantiate (2:=(_, _, _, _)). cbn. iModIntro. iSplits; ss; et. iFrame.
            des; clarify. apply Any.upcast_inj in H5. des; clarify.
            iSplitL.
            - iSplitR. { instantiate (1:=True%I); ss. } iRight. iRight. iSplits; ss; et.
              iDestruct "A" as "[A B]". iFrame.
            - iSplits; ss. { rewrite PURE2; ss. } iPureIntro. r in PURE. hexploit PURE; et. i; des_ifs. et. }
          { i. iIntros "H". ss. }
          fold wf. mDesAll; des; clarify. steps. astop. steps.

          hpost_tgt.
          { iModIntro. iFrame. iSplits; ss. iCombine "A1" "INV" as "A". iAssumption. }
          steps. fold wf. ss. des_ifs. rewrite _UNWRAPU. steps.
          hret None; ss.
          { iDes; ss; clarify. iModIntro. iSplits; ss; et. apply Any.upcast_inj in H6. des; clarify.
            iSplitR "A A1"; ss; et.
            - iLeft. iSplits; ss; et; iFrame.
            - iFrame. iSplits; ss; et. }
          { iDes; des; clarify. iPureIntro. r. fold wf in WF0. exists None; esplits; et. }
      }
      mDesOr "INVS"; mDesAll; des; clarify.
      { (* UNINIT *) mAssertPure False; ss. iApply (mw_state_false with "A1"); et. }
      { (* LOCKED *) mAssertPure False; ss. iApply (mw_state_false with "A1"); et. }
    }

    econs; ss.
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
