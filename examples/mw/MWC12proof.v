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
    (* clear. *)
    (* { r. i. autounfold with stb in *; autorewrite with stb in *. ss. des_ifs. *)
    (*   - r in PURE; des; ss; unfold is_pure in *. des_ifs. r in PURE. uipropall. des; clarify. *)
    (*   - r in PURE; des; ss; unfold is_pure in *. des_ifs. r in PURE. uipropall. des; clarify. *)
    (*   - r in PURE; des; ss; unfold is_pure in *. des_ifs. r in PURE. uipropall. des; clarify. *)
    (*   - r in PURE; des; ss; unfold is_pure in *. des_ifs. r in PURE. uipropall. des; clarify. *)
    (*   - r in PURE; des; ss; unfold is_pure in *. des_ifs. r in PURE. uipropall. des; clarify. *)
    (*   - r in PURE; des; ss; unfold is_pure in *. des_ifs. r in PURE. uipropall. des; clarify. *)
    (*   - r in PURE; des; ss; unfold is_pure in *. des_ifs. r in PURE. uipropall. des; clarify. *)
    (*   - r in PURE; des; ss; unfold is_pure in *. des_ifs. r in PURE. uipropall. des; clarify. *)
    (*   - r in PURE; des; ss; unfold is_pure in *. des_ifs. r in PURE. uipropall. des; clarify. *)
    (*   - r in PURE; des; ss; unfold is_pure in *. des_ifs. r in PURE. uipropall. des; clarify. *)
    (* } *)
    admit "uncomment".
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
    2: { esplits. econs; et. eapply to_semantic. iIntros "A".
         iSplitL; cycle 1.
         { iApply Own_unit; ss. }
         iRight. iSplits; ss; et. }


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
      { (* INIT *)
        mCombine "A" "INIT". mOwnWf "A". exfalso. admit "ez".
      }
      mDesOr "INVS"; mDesAll; des; clarify; steps.
      { (* UNINIT *)
        harg_tgt.
        { iModIntro. iFrame. iSplits; et. iCombine "A" "A1" as "A". iCombine "A" "A2" as "A". iAssumption. }
        steps.


        (*** calling APC ***)
        hAPC None; try assumption.
        { iIntros "[[A B] C]". iSplitL "C".
          - iRight. iLeft. iSplits; et.
          - iCombine "A" "B" as "A". iAssumption.
        }
        fold wf. steps. r in WLE. des_ifs. astart 1. astep "new" (([]: list val)↑). stb_tac. clarify.


        (*** calling Map.new ***)
        hcall _ _ _.
        {
          Ltac get_fresh_string :=
            match goal with
            | |- context["A"] =>
              match goal with
              | |- context["A0"] =>
                match goal with
                | |- context["A1"] =>
                  match goal with
                  | |- context["A2"] =>
                    match goal with
                    | |- context["A3"] =>
                      match goal with
                      | |- context["A4"] =>
                        match goal with
                        | |- context["A5"] => fail 5
                        | _ => constr:("A5")
                        end
                      | _ => constr:("A4")
                      end
                    | _ => constr:("A3")
                    end
                  | _ => constr:("A2")
                  end
                | _ => constr:("A1")
                end
              | _ => constr:("A0")
              end
            | _ => constr:("A")
            end
          .
          Ltac iDes :=
            repeat multimatch goal with
            | |- context[@environments.Esnoc _ _ (INamed ?namm) ?ip] =>
              match ip with
              | @bi_or _ _ _ =>
                let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ "|" +:+ namm +:+ "]")) in
                iDestruct namm as pat
              | @bi_pure _ _ => iDestruct namm as "%"
              | @iNW _ ?newnamm _ => iEval (unfold iNW) in namm; iRename namm into newnamm
              | @bi_sep _ _ _ =>
                let f := get_fresh_string in
                let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ " " +:+ f +:+ "]")) in
                iDestruct namm as pat
              | @bi_exist _ _ (fun x => _) =>
                let x := fresh x in
                iDestruct namm as (x) namm
              end
            end
          .
          iDes; ss; des; clarify.
          { iCombine "INIT" "A" as "A". iOwnWf "A". exfalso. admit "ez". }
          iModIntro. iSplits; ss. iSplitL "A0".
          { iAssumption. }
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
          iCombine "A1" "INV" as "A". iCombine "A" "FR" as "A". iAssumption.
        }
        fold wf. steps. stb_tac; ss; clarify. steps. hide_k.



        (*** calling App.init ***)
        hcall _ _ _.
        { iDes; ss; des; clarify. apply Any.upcast_inj in H6. des; clarify. clear_fast.
          iModIntro. iSplits; ss; et.
          iSplitR "LOCKED A"; cycle 1.
          { iFrame. iSplits; ss; et. }
          iSplitR.
          { instantiate (1:=True%I); ss. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { esplits; ss; et. }
        { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
        unhide_k. steps. fold wf. mDesAll. des; clarify.



        hpost_tgt.
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et.
          iCombine "A1" "POST" as "A". iCombine "A" "INV" as "A". iAssumption.
        }
        fold wf. steps. force_l; stb_tac; ss; clarify. steps. rewrite _UNWRAPU. steps.
        stb_tac; clarify.



        (*** calling loop ***)
        Opaque Z.eq_dec.
        hcall _ _ _.
        { iDes; ss; des; clarify; cycle 1.
          { iCombine "FR A0" as "B". iOwnWf "B". exfalso. admit "ez". }
          iModIntro. iSplits; ss; et. iSplitR "A1 FR"; cycle 1.
          { iSplits; ss; et. iFrame. iSplits; ss; et. }
          iSplitR.
          { instantiate (1:=True%I); ss. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { esplits; ss; et. }
        { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
        steps. fold wf. mDesAll. des; clarify.

        hpost_tgt.
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et.
          iCombine "A1" "INV" as "A". iCombine "A2" "A" as "A". iAssumption. }
        steps. fold wf.


        (*** returning ***)
        hret None; ss.
        { iModIntro. iDes; ss; clarify; cycle 1.
          { iCombine "A A1" as "B". iOwnWf "B". exfalso. admit "ez". }
          iFrame.
          iSplitL; cycle 1.
          { iSplits; ss; et. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { iDestruct "Q" as "%". iPureIntro. clarify. r. fold wf in WF0. exists None; esplits; et. }
      }
      { (* LOCKED *)
        mCombine "A" "A2". mOwnWf "A". exfalso. admit "ez".
      }
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
        { iModIntro. iFrame. iSplits; et.
          iCombine "A" "A1" as "A". iCombine "A" "A2" as "A". iCombine "A" "INIT" as "A". iAssumption. }
        steps. stb_tac; ss; clarify.

        hcall _ _ _.
        { iDes. iModIntro. iFrame. iSplits; ss; et. iSplitR.
          { instantiate (1:=True%I); ss. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { esplits; ss; et. }
        { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
        fold wf. steps. mDesAll; des; clarify. force_l; stb_tac; ss; clarify. steps.


        hpost_tgt.
        { iModIntro. iFrame. iSplits; ss; et.
          iCombine "A1 POST" as "A". iCombine "INV A" as "A". iAssumption. }
        fold wf. steps. rewrite _UNWRAPU. steps. stb_tac; ss; clarify.


        hcall _ _ _.
        { iDes; ss; cycle 1.
          { iCombine "A" "A1" as "A". iOwnWf "A". admit "ez". }
          iModIntro. iFrame. iSplits; ss; et. iSplitR.
          { instantiate (1:=True%I); ss. }
          iLeft. iSplits; ss; et. iFrame.
        }
        { esplits; ss; et. }
        { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
        fold wf. steps. mDesAll; des; clarify. rewrite Any.upcast_downcast in *. clarify.

        hpost_tgt.
        { iModIntro. iFrame. iSplits ;ss; et. iCombine "A2 A1" as "A". iCombine "INV A" as "A". iAssumption. }
        fold wf. steps.


        hret None; ss.
        { iDes; ss; clarify; cycle 1.
          { iCombine "A1 A0" as "B". iOwnWf "B". exfalso. admit "ez". }
          iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. iLeft. iSplits; ss; et. iFrame.
        }
        { iDestruct "Q" as "%". iPureIntro. clarify. r. fold wf in WF0. exists None; esplits; et. }
      }
      mDesOr "INVS"; mDesAll; des; clarify; steps.
      { (* UNINIT *)
        mCombine "A" "A2". mOwnWf "A". exfalso. admit "ez".
      }
      { (* LOCKED *)
        mCombine "A" "LOCKED". mOwnWf "A". exfalso. admit "ez".
      }
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
        { iApply (mw_state_eq with "A"). iFrame. }
        subst. rename a into full.
        steps.
        rename a2 into lst0. rename z0 into k. rename z into v.
        change (λ k1 : Z, if dec k k1 then Some v else full k1) with (add k v full).
        harg_tgt.
        { iPoseProof ((mw_state_upd _ _ (add k v full)) with "A INIT") as "A".
          iMod "A". iModIntro. iFrame. iSplits; ss; et.
          iCombine "A" "A1" as "A". iAssumption. }
        fold wf. steps.
        destruct (dec (lst_cls lst0 k) uninit).
        - steps.
          unfold set. destruct (dec k k); ss. destruct x; steps.
          + hAPC _; ss.
            { iIntros "[[A B] C]". iSplitL "A B".
              - iRight. iRight. iSplits; et. iFrame.
              - iAssumption.
            }
            steps. fold wf. r in WLE. des_ifs.
            

            hret None; ss.
            { iDes; ss; clarify. apply Any.upcast_inj in H5. des; clarify.
              iModIntro. iFrame. iSplits; ss; et. iLeft. iSplits; ss; et.
              { iFrame. iAssumption. }
              clear - PURE. iPureIntro. r. r in PURE. ss. i. specialize (PURE k0 v0). des_ifs; et.
            }
            { iDestruct "Q" as "%". iPureIntro. clarify. r. fold wf in WF0. exists None; esplits; et. }
          + steps.
            astart 1. astep "update" ([lst_map lst0; Vint k; Vint v]↑). stb_tac; ss; clarify.
            hcall _ _ (Some (_, _)).
            { iDes; clarify. instantiate (2:=(_, _, _, _)). cbn. iModIntro. iSplits; ss; et. iFrame.
              iSplitL.
              - iSplitR. { instantiate (1:=True%I); ss. } iRight. iRight. iSplits; ss; et. iSplitL "FR"; ss.
              - iSplits; ss; et. rewrite PURE2; ss.
            }
            { esplits; ss; et. }
            { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
            fold wf. mDesAll; des; clarify. steps. astop. steps.

            hpost_tgt.
            { iModIntro. iFrame. iSplits; ss. iCombine "A1" "INV" as "A". iAssumption. }
            steps. fold wf. ss. des_ifs.
            hret None; ss.
            { iDes; ss; clarify. iModIntro. iSplits; ss; et. apply Any.upcast_inj in H5. des; clarify.
              iSplitR "A"; ss; et. iLeft. iSplits; ss; et; iFrame.
              clear - PURE. iPureIntro. r. r in PURE. ss. i. specialize (PURE k0 v0). des_ifs; et.
            }
            { iDestruct "Q" as "%". iPureIntro. clarify. r. fold wf in WF0. exists None; esplits; et. }
        - steps.
          destruct (lst_cls lst0 k) eqn:T; ss.
          + steps. hAPC _; ss.
            { iIntros "[[A B] C]". iSplitL "A B".
              - iRight. iRight. iSplits; et. iFrame.
              - iAssumption.
            }
            steps. fold wf. r in WLE. des_ifs.
            

            hret None; ss.
            { iDes; ss; clarify. apply Any.upcast_inj in H5. des; clarify.
              iModIntro. iFrame. iSplits; ss; et. iLeft. iSplits; ss; et.
              { iFrame. iAssumption. }
              clear - T PURE. iPureIntro. r. r in PURE. ss. i. specialize (PURE k0 v0). unfold set.
              des_ifs; et; try congruence.
            }
            { iDestruct "Q" as "%". iPureIntro. clarify. r. fold wf in WF0. exists None; esplits; et. }
          + steps.
            astart 1. astep "update" ([lst_map lst0; Vint k; Vint v]↑). stb_tac; ss; clarify.
            hcall _ _ (Some (_, _)).
            { iDes; clarify. instantiate (2:=(_, _, _, _)). cbn. iModIntro. iSplits; ss; et. iFrame.
              iSplitL.
              - iSplitR. { instantiate (1:=True%I); ss. } iRight. iRight. iSplits; ss; et. iSplitL "FR"; ss.
              - iSplits; ss; et. rewrite PURE2; ss.
            }
            { esplits; ss; et. }
            { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
            fold wf. mDesAll; des; clarify. steps. astop. steps.

            hpost_tgt.
            { iModIntro. iFrame. iSplits; ss. iCombine "A1" "INV" as "A". iAssumption. }
            steps. fold wf. ss. des_ifs.
            hret None; ss.
            { iDes; ss; clarify. iModIntro. iSplits; ss; et. apply Any.upcast_inj in H5. des; clarify.
              iSplitR "A"; ss; et. iLeft. iSplits; ss; et; iFrame.
              clear - T PURE. iPureIntro. r. r in PURE. ss. i. specialize (PURE k0 v0).
              des_ifs; et; try congruence.
            }
            { iDestruct "Q" as "%". iPureIntro. clarify. r. fold wf in WF0. exists None; esplits; et. }
      }
      mDesOr "INVS"; mDesAll; des; clarify.
      { (* UNINIT *) mAssertPure False; ss. iApply (mw_state_false with "A"); et. }
      { (* LOCKED *) mAssertPure False; ss. iApply (mw_state_false with "A"); et. }
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
        { iApply (mw_state_eq with "A"). iFrame. }
        subst. rename a into full.
        steps.
        rename a2 into lst0. rename z0 into k. rename z into v.
        rewrite PURE1. steps.

        harg_tgt.
        { iModIntro. iFrame. iSplits; ss; et. iCombine "A" "A1" as "A". iCombine "INIT A" as "A". iAssumption. }
        steps. fold wf. force_r.
        { exploit PURE; et. i. des_ifs. }
        steps.
        des_ifs.
        - steps. hAPC (Some (_, _)); ss.
          { iIntros "[A [B C]]". iSplitR "C"; try iAssumption. iRight. iRight. iSplits; ss; et. iFrame. }
          fold wf. steps.
          assert(T: lst_opt lst0 k = (Vint v)).
          { r in PURE. exploit PURE; et. i; des_ifs. }
          rewrite T. steps.
          hret None; ss.
          { iDes; ss; clarify. iModIntro. apply Any.upcast_inj in H5. des; clarify. iFrame. iSplits; ss; et.
            iLeft. iSplits; ss; et. { iFrame. } admit "TODO". }
          { iDestruct "Q" as "%". iPureIntro. clarify. r. fold wf in WF0. exists None; esplits; et. }
        - steps. astart 1. astep "access" ([lst_map lst0; Vint k]↑). stb_tac; ss; clarify.
          hcall _ _ (Some (_, _)).
          { iDes; clarify. instantiate (2:=(_, _, _, _)). cbn. iModIntro. iSplits; ss; et. iFrame.
            des; clarify. apply Any.upcast_inj in H3. des; clarify.
            iSplitL.
            - iSplitR. { instantiate (1:=True%I); ss. } iRight. iRight. iSplits; ss; et. iFrame.
            - iSplits; ss. { rewrite PURE2; ss. } iPureIntro. r in PURE. hexploit PURE; et. i; des_ifs. et. }
          { esplits; ss; et. }
          { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
          fold wf. mDesAll; des; clarify. steps. astop. steps.

          hpost_tgt.
          { iModIntro. iFrame. iSplits; ss. iCombine "A1" "INV" as "A". iAssumption. }
          steps. fold wf. ss. des_ifs.
          hret None; ss.
          { iDes; ss; clarify. iModIntro. iSplits; ss; et. apply Any.upcast_inj in H5. des; clarify.
            iSplitR "A"; ss; et. iLeft. iSplits; ss; et; iFrame. iFrame. iSplits; ss; et. admit "TODO". }
          { iDestruct "Q" as "%". iPureIntro. clarify. r. fold wf in WF0. exists None; esplits; et. }
      }
      mDesOr "INVS"; mDesAll; des; clarify.
      { (* UNINIT *) mAssertPure False; ss. iApply (mw_state_false with "A"); et. }
      { (* LOCKED *) mAssertPure False; ss. iApply (mw_state_false with "A"); et. }
    }

    econs; ss.
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
