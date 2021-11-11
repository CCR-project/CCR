Require Import HoareDef MWHeader MWC2 MWC1 SimModSem.
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

Require Import HTactics2 ProofMode STB.
Require Import Mem1.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Context `{@GRA.inG AppRA.t Σ}.
  Context `{@GRA.inG mwRA Σ}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG mapRA Σ}.
  Context `{@GRA.inG spRA Σ}.

  Let W: Type := Any.t * Any.t.

  (***
BOTTOM LINE: We should relate uninit state explicitly - its physical states are (tt), (tt)

(1) after init
  cls, opt, map == full
  Own (black f)
  f == full
(2) uninit
  mp_src = mp_tgt = tt
  Own (black f) * Own (white f)
  f == empty

{ Init } main { Run }
{ white f } get { white f }
{ white f } put { white f }

TODO: APC, locked thinges
   ***)

  (* Definition sim_mw (f: Z -> option Z) (st: Z -> Z): Prop := *)
  (*   forall k v, f k = Some v -> st k = v *)
  (* . *)

  Let trans (f: Z -> option Z): Z -> Z := fun k => or_else (f k) 0.

  (* Definition sim (f: Z -> option Z) (map: list (Z * Z)) (lst0: local_state): iProp := *)
  (*   (∀ k v (IN: f k = Some v), *)
  (*       match lst0.(lst_cls) k with *)
  (*       | uninit => ⌜False⌝%I *)
  (*       | opt => ⌜lst0.(lst_opt) k = Vint v⌝ *)
  (*       | normal => ⌜alist_find k map = Some v⌝%I *)
  (*       end *)
  (*   )%I *)
  (* . *)
  Definition sim (f map: Z -> option Z) (lst0: local_state): Prop :=
    (∀ k v (IN: f k = Some v),
        match lst0.(lst_cls) k with
        | uninit => False
        | opt => lst0.(lst_opt) k = Vint v
        | normal => map k = Some v
        end
    )
  .

  (*** st_src = mw_state = mw_stateX
       st_tgt = w0
   ***)

  (*** TODO: redundant with Invariant.v. Make it as a pattern (write sth like Invariant2.v) ***)
  Definition le (w0 w1: option (Any.t * Any.t)): Prop :=
    match w0, w1 with
    | Some w0, Some w1 => w0 = w1
    | None, None => True
    | _, _ => False
    end
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. unfold le. ii. des_ifs. Qed.
  Next Obligation. unfold le. ii. des_ifs. Qed.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      (option (Any.t * Any.t))
      (fun w0 st_src st_tgt => (
           {{"INIT": ∃ f h map lst0, OwnM (mw_stateX f) ** OwnM (is_map h map)
                        ** ⌜st_src = f↑⌝ ** ⌜st_tgt = lst0↑⌝ ** ⌜w0 = None⌝
                        ** ⌜lst0.(lst_map) = Vptr h 0%Z⌝ ** ⌜sim f map lst0⌝}} ∨
           {{"UNINIT": ⌜st_src = (Maps.empty (K:=Z) (V:=Z))↑ ∧ st_tgt = tt↑⌝ ** ⌜w0 = None⌝
                        ** OwnM (mw_state Maps.empty)
           }} ∨
           {{"LOCKED": ∃ f, OwnM (mw_state f) ** OwnM (mw_stateX f) **
                            ⌜st_src = f↑⌝ ** ⌜w0 = Some (st_src, st_tgt)⌝}}
         )%I)
  .

  Let PURENICL: stb_pure_incl (to_stb MW1Stb) (to_stb (MWStb ++ AppStb ++ MapStb ++ MemStb)).
  Proof.
    clear.
    { r. i. autounfold with stb in *; autorewrite with stb in *. ss.
      des_ifs; (r in PURE; des; ss; unfold is_pure in *; des_ifs;
                r in PURE; uipropall; des; clarify; r in PURE1; uipropall; des; clarify).
    }
  Qed.

  Global Opaque bi_exist bi_sep OwnM Own.
  (*** TODO: put this somewhere else. Without this, iCombine gives later modality. ***)




  (* Variable global_stb: Sk.t -> gname -> option fspec. *)
  (* Hypothesis STBINCL: forall sk, stb_incl (to_stb MWStb1) (global_stb sk). *)

  (* Theorem correct: refines2 [MWC1.MW global_stb] [MWC2.MW global_stb]. *)
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

      unfold mainF, MWC2.mainF, ccallU.

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
        hcall _ _ _.
        {
          iDes; ss; des; clarify.
          { iExFalso. iApply (mw_stateX_false with "INIT"); et. }
          iModIntro. iSplits; ss. iSplitL "A".
          { xtra. }
          { iRight. iRight. iSplits; ss; et. iFrame. }
        }
        { esplits; ss; et. }
        { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
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
        hcall _ _ _.
        { iDes; ss; des; clarify. apply Any.upcast_inj in H7. des; clarify. clear_fast.
          iModIntro. iSplits; ss; et.
          iSplitR "LOCKED A A0"; cycle 1.
          { iFrame. iSplits; ss; et. }
          iSplitR.
          { instantiate (1:=True%I); ss. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { esplits; ss; et. }
        { i. iIntros "H". ss. iDes; des; clarify. }
        unhide_k. steps. fold wf. mDesAll. des; clarify.



        hpost_tgt.
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. xtra. }
        fold wf. steps. force_l; stb_tac; ss; clarify. steps. rewrite _UNWRAPU. steps.
        stb_tac; clarify.



        (*** calling loop ***)
        Opaque Z.eq_dec.
        hcall _ _ _.
        { iDes; ss; des; clarify; cycle 1.
          { iExFalso. iApply (mw_state_false with "FR"); et. }
          iModIntro. iSplits; ss; et. iSplitR "A A0 FR"; cycle 1.
          { iSplits; ss; et. iFrame. iSplits; ss; et. }
          iSplitR.
          { instantiate (1:=True%I); ss. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { esplits; ss; et. }
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

      unfold loopF, MWC2.loopF, ccallU.

      harg. fold wf. mDesAll; des; clarify.
      mDesOr "INVS"; mDesAll; des; clarify; steps.
      { (* INIT *)
        force_l; stb_tac; ss; clarify. steps.
        harg_tgt.
        { iModIntro. iFrame. iSplits; et. xtra. }
        steps. stb_tac; ss; clarify.

        hcall _ _ _.
        { iDes. iModIntro. iFrame. iSplits; ss; et. iSplitR.
          { instantiate (1:=True%I); ss. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { esplits; ss; et. }
        { i. iIntros "H". ss. iDes; des; clarify. }
        fold wf. steps. mDesAll; des; clarify. force_l; stb_tac; ss; clarify. steps.


        hpost_tgt.
        { iModIntro. iFrame. iSplits; ss; et. xtra. }
        fold wf. steps. rewrite _UNWRAPU. steps. stb_tac; ss; clarify.


        hcall _ _ _.
        { iDes; ss; cycle 1.
          { iExFalso. iApply (mw_state_false with "FR"); et. }
          iModIntro. iFrame. iSplits; ss; et. iSplitR.
          { instantiate (1:=True%I); ss. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { esplits; ss; et. }
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

      unfold putF, MWC2.putF, ccallU.

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
            hcall _ _ (Some (_, _)).
            { iDes; clarify. instantiate (2:=(_, _, _, _)). cbn. iModIntro. iSplits; ss; et. iFrame.
              iSplitL.
              - iSplitR. { instantiate (1:=True%I); ss. } iRight. iRight. iSplits; ss; et. iSplitL "A"; ss.
              - iSplits; ss; et. rewrite PURE2; ss.
            }
            { esplits; ss; et. }
            { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
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
            hcall _ _ (Some (_, _)).
            { iDes; clarify. instantiate (2:=(_, _, _, _)). cbn. iModIntro. iSplits; ss; et. iFrame.
              iSplitL.
              - iSplitR. { instantiate (1:=True%I); ss. } iRight. iRight. iSplits; ss; et. iSplitL "A"; ss.
              - iSplits; ss; et. rewrite PURE2; ss.
            }
            { esplits; ss; et. }
            { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
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

      unfold getF, MWC2.getF, ccallU.

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
          hcall _ _ (Some (_, _)).
          { iDes; clarify. instantiate (2:=(_, _, _, _)). cbn. iModIntro. iSplits; ss; et. iFrame.
            des; clarify. apply Any.upcast_inj in H4. des; clarify.
            iSplitL.
            - iSplitR. { instantiate (1:=True%I); ss. } iRight. iRight. iSplits; ss; et.
              iDestruct "A" as "[A B]". iFrame.
            - iSplits; ss. { rewrite PURE2; ss. } iPureIntro. r in PURE. hexploit PURE; et. i; des_ifs. et. }
          { esplits; ss; et. }
          { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
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
