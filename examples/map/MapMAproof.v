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

  Definition map_of_list (l: list Z): iProp :=
    OwnM (Excl.unit,
           Auth.excl
             ((fun n => match nth_error l n with
                        | Some v => Excl.unit
                        | None => Excl.just 0%Z
                        end): @URA.car (nat ==> (Excl.t Z))%ra)
             ((fun n => match nth_error l n with
                        | Some v => Excl.just v
                        | None => Excl.just 0%Z
                        end): @URA.car (nat ==> (Excl.t Z))%ra)).

  Lemma map_of_list_initialize sz
    :
    map_of_list [] -∗ #=> (map_of_list (List.repeat 0%Z sz) ** initial_points_tos sz).
  Proof.
  Admitted.

  Lemma map_of_list_get l k v
    :
    map_of_list l -∗ map_points_to k v -∗ (map_of_list l ** map_points_to k v ** (⌜nth_error l k = Some v⌝)).
  Proof.
  Admitted.

  Lemma map_of_list_set l k v
    :
    map_of_list l -∗ (∃ v, map_points_to k v) -∗ #=> (∃ l', map_of_list l' ** map_points_to k v ** (⌜set_nth k l v = Some l'⌝)).
  Proof.
  Admitted.

  Let wf: _ -> W -> Prop :=
        @mk_wf
          _ unit
          (fun _ st_src st_tgt =>
             ((∃ f l, ⌜st_src = f↑ /\ st_tgt = l↑ /\ (forall k v (GET: nth_error l k = Some v), f k = v)⌝ ** map_of_list l) ∨ (map_of_list []))%I).

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Theorem correct: refines2 [MWC1.MW] [MWC2.MW].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=le); ss.
    { typeclasses eauto. }
    2: { esplits. econs; et. eapply to_semantic. iIntros "[A B]". iSplitL "B"; et. iRight. iSplits; ss; et. }


    econs.
    {
      (*** init ***)
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)

      unfold mainF, MWC2.mainF, ccallU, ccallN.

      harg. fold wf.
      mDesAll; des; clarify.
      mDesOr "INVS"; mDesAll; des; clarify; steps.
      { (* INIT *)  mAssertPure False; ss. iApply (mw_stateX_false with "INIT"); et. }
      mDesOr "INVS"; mDesAll; des; clarify; steps.
      { (* UNINIT *)
        harg_tgt.
        { iModIntro. iFrame. iSplits; et. xtra. }
        steps.


        (*** calling APC ***)
        hAPC None; try assumption.
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
