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
                        ** ⌜st_src = (trans f)↑⌝ ** ⌜st_tgt = lst0↑⌝ ** ⌜w0 = None⌝
                        ** ⌜lst0.(lst_map) = Vptr h 0%Z⌝ ** ⌜sim f map lst0⌝}} ∨
           {{"UNINIT": ⌜st_src = (fun (_:Z) => 0%Z)↑ ∧ st_tgt = tt↑⌝ ** ⌜w0 = None⌝
                        ** OwnM (mw_state Maps.empty)
           }} ∨
           {{"LOCKED": ∃ f, OwnM (mw_state f) ** OwnM (mw_stateX f) **
                            ⌜st_src = (trans f)↑⌝ ** ⌜w0 = Some (st_src, st_tgt)⌝}}
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

  Global Opaque OwnM Own. (*** TODO: put this somewhere else. Without this, iCombine gives later modality. ***)




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
        { iFrame. iSplits; et. iCombine "A" "A1" as "A". iCombine "A" "A2" as "A". iAssumption. }
        steps.


        (*** calling APC ***)
        hAPC (Some (_, _)); try assumption.
        { iIntros "[[A B] C]". iSplitR "B".
          - iRight. iRight. iSplits; et. { iFrame. } iSplits; ss.
          - iAssumption.
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
            (* | |- environments.envs_entails ?a _ => idtac a *)
            (* | |- context[@environments.Esnoc _ _ ?namm ?ip] => idtac namm; idtac ip *)
            | |- context[@environments.Esnoc _ _ (INamed ?namm) ?ip] =>
              match ip with
              | @bi_or _ _ _ =>
                let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ "|" +:+ namm +:+ "]")) in
                iDestruct namm as pat
              | @bi_pure _ _ => iDestruct namm as "%"
              | @iNW _ ?newnamm _ => iEval (unfold iNW) in namm; iRename namm into newnamm
              | @bi_sep _ _ _ =>
                (* iDestruct namm as "[? ?]" *)
                (* let namm2 := iFresh in *)
                (* let pat := constr:("[" +:+ namm +:+ " " +:+ namm2 +:+ "]") in *)
                (* let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ " " +:+ namm +:+ "]")) in *)


                (* let pat := constr:("[" +:+ ltac:(get_fresh_string) +:+ " ?]") in *)
                let f := get_fresh_string in
                let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ " " +:+ f +:+ "]")) in
                (* let pat := constr:("[" +:+ "A" +:+ " ?]") in *)
                (* idtac pat; *)
                iDestruct namm as pat
                      (* iDestruct namm as pat *)
              | @bi_exist _ _ (fun x => _) =>
                let x := fresh x in
                iDestruct namm as (x) namm
              end
            end
          .
          iDes; ss.
          iDes.
          match goal with
          | |- context[@environments.Esnoc _ _ (INamed ?naeme) ?ip] =>
            match ip with
              | @bi_exist _ _ (fun x => _) =>
                (* idtac name; idtac x; *)
                (* let x := fresh x in *)
                iDestruct "INIT" as (f) "B"
              end
            end
          .
          iDestruct "INIT" as (f) "INIT".
          iDestruct "INIT" as (f) "INIT".
    | H : exists x, NW (fun y => _) |- _ =>
      let x' := fresh x in let y' := fresh y in destruct H as [x' y']; red in y'
          Set Printing All.
                  (@bi_exist (@iProp Σ) (forall _ : Z, option Z)
                     (fun f : forall _ : Z, option Z =>
          iDestruct "INIT" as (f) "INIT".
          Ltac iCounter :=
            match goal with
            | |- context[@environments.Envs _ _ _ ?a ] => idtac a
            end
          .
          iDes.
          Set Printing All.
          environments.envs_entails

(INamed (String (Ascii.Ascii false false false false true false true false) EmptyString))
(@bi_pure (@iProp Σ)
   (and (@eq Any.t (@Any.upcast (list val) (@nil val)) (@Any.upcast (list val) (@nil val))) (@eq ord o_tgt ord_top)))
(INamed
   (String (Ascii.Ascii false true true false false false true false)
      (String (Ascii.Ascii false true false false true false true false) EmptyString)))
(@bi_sep (@iProp Σ)
   (@bi_or (@iProp Σ)
      (@iNW Σ
         (String (Ascii.Ascii true false false true false false true false)
            (String (Ascii.Ascii false true true true false false true false)
               (String (Ascii.Ascii true false false true false false true false)
                  (String (Ascii.Ascii false false true false true false true false) EmptyString))))
         (@bi_exist (@iProp Σ) (forall _ : Z, option Z)
            (fun f : forall _ : Z, option Z =>
             @bi_exist (@iProp Σ) nat
               (fun h : nat =>
                @bi_exist (@iProp Σ) (forall _ : Z, option Z)
                  (fun map : forall _ : Z, option Z =>
                   @bi_exist (@iProp Σ) local_state
                     (fun lst0 : local_state =>
                      @bi_sep (@iProp Σ)
                        (@bi_sep (@iProp Σ)
                           (@bi_sep (@iProp Σ)
                              (@bi_sep (@iProp Σ)
                                 (@bi_sep (@iProp Σ)
                                    (@bi_sep (@iProp Σ) (@OwnM Σ mwRA H0 (mw_stateX f))
                                       (@OwnM Σ mapRA H2 (is_map h map)))
                                    (@bi_pure (@iProp Σ)
                                       (@eq Any.t mp_src1 (@Any.upcast (forall _ : Z, Z) (trans f)))))
                                 (@bi_pure (@iProp Σ) (@eq Any.t mp_tgt1 (@Any.upcast local_state lst0))))
                              (@bi_pure (@iProp Σ)
                                 (@eq (option (prod Any.t Any.t))
                                    (@Some (prod Any.t Any.t)
                                       (@pair Any.t Any.t (@Any.upcast (forall _ : Z, Z) (fun _ : Z => Z0))
                                          (@Any.upcast unit tt))) (@None (prod Any.t Any.t)))))
                           (@bi_pure (@iProp Σ) (@eq val (lst_map lst0) (Vptr h Z0))))
                        (@bi_pure (@iProp Σ) (sim f map lst0))))))))
      (@bi_or (@iProp Σ)
         (@iNW Σ
            (String (Ascii.Ascii true false true false true false true false)
               (String (Ascii.Ascii false true true true false false true false)
                  (String (Ascii.Ascii true false false true false false true false)
                     (String (Ascii.Ascii false true true true false false true false)
                        (String (Ascii.Ascii true false false true false false true false)
                           (String (Ascii.Ascii false false true false true false true false) EmptyString))))))
            (@bi_sep (@iProp Σ)
               (@bi_sep (@iProp Σ)
                  (@bi_pure (@iProp Σ)
                     (and (@eq Any.t mp_src1 (@Any.upcast (forall _ : Z, Z) (fun _ : Z => Z0)))
                        (@eq Any.t mp_tgt1 (@Any.upcast unit tt))))
                  (@bi_pure (@iProp Σ)
                     (@eq (option (prod Any.t Any.t))
                        (@Some (prod Any.t Any.t)
                           (@pair Any.t Any.t (@Any.upcast (forall _ : Z, Z) (fun _ : Z => Z0))
                              (@Any.upcast unit tt))) (@None (prod Any.t Any.t)))))
               (@OwnM Σ mwRA H0 (mw_state (fun _ : Z => @None Z)))))
         (@iNW Σ
            (String (Ascii.Ascii false false true true false false true false)
               (String (Ascii.Ascii true true true true false false true false)
                  (String (Ascii.Ascii true true false false false false true false)
                     (String (Ascii.Ascii true true false true false false true false)
                        (String (Ascii.Ascii true false true false false false true false)
                           (String (Ascii.Ascii false false true false false false true false) EmptyString))))))
            (@bi_exist (@iProp Σ) (forall _ : Z, option Z)
               (fun f : forall _ : Z, option Z =>
                @bi_sep (@iProp Σ)
                  (@bi_sep (@iProp Σ)
                     (@bi_sep (@iProp Σ) (@OwnM Σ mwRA H0 (mw_state f)) (@OwnM Σ mwRA H0 (mw_stateX f)))
                     (@bi_pure (@iProp Σ) (@eq Any.t mp_src1 (@Any.upcast (forall _ : Z, Z) (trans f)))))
                  (@bi_pure (@iProp Σ)
                     (@eq (option (prod Any.t Any.t))
                        (@Some (prod Any.t Any.t)
                           (@pair Any.t Any.t (@Any.upcast (forall _ : Z, Z) (fun _ : Z => Z0))
                              (@Any.upcast unit tt)))
                        (@Some (prod Any.t Any.t) (@pair Any.t Any.t mp_src1 mp_tgt1)))))))))
   (@OwnM Σ AppRA.t H Init))








          (@environments.Esnoc (bi_car (@iProp Σ)) (@environments.Enil (bi_car (@iProp Σ)))
             (INamed
                (String (Ascii.Ascii false true true false false false true false)
                   (String (Ascii.Ascii false true false false true false true false) EmptyString)))
             (@bi_sep (@iProp Σ)
                (@bi_or (@iProp Σ)
                   (@iNW Σ
                      (String (Ascii.Ascii true false false true false false true false)
                         (String (Ascii.Ascii false true true true false false true false)
                            (String (Ascii.Ascii true false false true false false true false)
                               (String (Ascii.Ascii false false true false true false true false) EmptyString))))
                      (@bi_exist (@iProp Σ) (forall _ : Z, option Z)
                         (fun f : forall _ : Z, option Z =>
                          @bi_exist (@iProp Σ) nat
                            (fun h : nat =>
                             @bi_exist (@iProp Σ) (forall _ : Z, option Z)
                               (fun map : forall _ : Z, option Z =>
                                @bi_exist (@iProp Σ) local_state
                                  (fun lst0 : local_state =>
                                   @bi_sep (@iProp Σ)
                                     (@bi_sep (@iProp Σ)
                                        (@bi_sep (@iProp Σ)
                                           (@bi_sep (@iProp Σ)
                                              (@bi_sep (@iProp Σ)
                                                 (@bi_sep (@iProp Σ) (@OwnM Σ mwRA H0 (mw_stateX f))
                                                    (@OwnM Σ mapRA H2 (is_map h map)))
                                                 (@bi_pure (@iProp Σ)
                                                    (@eq Any.t mp_src1 (@Any.upcast (forall _ : Z, Z) (trans f)))))
                                              (@bi_pure (@iProp Σ)
                                                 (@eq Any.t mp_tgt1 (@Any.upcast local_state lst0))))
                                           (@bi_pure (@iProp Σ)
                                              (@eq (option (prod Any.t Any.t))
                                                 (@Some (prod Any.t Any.t)
                                                    (@pair Any.t Any.t
                                                       (@Any.upcast (forall _ : Z, Z) (fun _ : Z => Z0))
                                                       (@Any.upcast unit tt))) (@None (prod Any.t Any.t)))))
                                        (@bi_pure (@iProp Σ) (@eq val (lst_map lst0) (Vptr h Z0))))
                                     (@bi_pure (@iProp Σ) (sim f map lst0))))))))
                   (@bi_or (@iProp Σ)
                      (@iNW Σ
                         (String (Ascii.Ascii true false true false true false true false)
                            (String (Ascii.Ascii false true true true false false true false)
                               (String (Ascii.Ascii true false false true false false true false)
                                  (String (Ascii.Ascii false true true true false false true false)
                                     (String (Ascii.Ascii true false false true false false true false)
                                        (String (Ascii.Ascii false false true false true false true false)
                                           EmptyString))))))
                         (@bi_sep (@iProp Σ)
                            (@bi_sep (@iProp Σ)
                               (@bi_pure (@iProp Σ)
                                  (and (@eq Any.t mp_src1 (@Any.upcast (forall _ : Z, Z) (fun _ : Z => Z0)))
                                     (@eq Any.t mp_tgt1 (@Any.upcast unit tt))))
                               (@bi_pure (@iProp Σ)
                                  (@eq (option (prod Any.t Any.t))
                                     (@Some (prod Any.t Any.t)
                                        (@pair Any.t Any.t (@Any.upcast (forall _ : Z, Z) (fun _ : Z => Z0))
                                           (@Any.upcast unit tt))) (@None (prod Any.t Any.t)))))
                            (@OwnM Σ mwRA H0 (mw_state (fun _ : Z => @None Z)))))
                      (@iNW Σ
                         (String (Ascii.Ascii false false true true false false true false)
                            (String (Ascii.Ascii true true true true false false true false)
                               (String (Ascii.Ascii true true false false false false true false)
                                  (String (Ascii.Ascii true true false true false false true false)
                                     (String (Ascii.Ascii true false true false false false true false)
                                        (String (Ascii.Ascii false false true false false false true false)
                                           EmptyString))))))
                         (@bi_exist (@iProp Σ) (forall _ : Z, option Z)
                            (fun f : forall _ : Z, option Z =>
                             @bi_sep (@iProp Σ)
                               (@bi_sep (@iProp Σ)
                                  (@bi_sep (@iProp Σ) (@OwnM Σ mwRA H0 (mw_state f))
                                     (@OwnM Σ mwRA H0 (mw_stateX f)))
                                  (@bi_pure (@iProp Σ)
                                     (@eq Any.t mp_src1 (@Any.upcast (forall _ : Z, Z) (trans f)))))
                               (@bi_pure (@iProp Σ)
                                  (@eq (option (prod Any.t Any.t))
                                     (@Some (prod Any.t Any.t)
                                        (@pair Any.t Any.t (@Any.upcast (forall _ : Z, Z) (fun _ : Z => Z0))
                                           (@Any.upcast unit tt)))
                                     (@Some (prod Any.t Any.t) (@pair Any.t Any.t mp_src1 mp_tgt1)))))))))
                (@OwnM Σ AppRA.t H Init)))
            intros; unfold NW, iNW;
            repeat match goal with
                   | [ |- @ex _ _ ] => eexists
                   | [ |- _ /\ _ ] => split
                   | [ |- @sig _ _ ] => eexists
                   | [ |- @sigT _ _ ] => eexists
                   | [ |- @prod _  _ ] => split
                   | |- environments.envs_entails _ (@bi_exist _ _ _) => iExists _
                   | _ => iSplit
                   end
          .
          iDestruct "FR" as "[[A|A] B]".
          iDestruct "FR" as "[A [B C]]". iModIntro. iFrame. iSplits; ss. iCombine "B" "C" as "A". iApply "A". }
        { esplits; ss; et. }
        { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }

        fold wf. steps. astop. steps. mDesAll; des; clarify.
        force_l; stb_tac; ss; clarify. steps.

        hpost_tgt.
        { iFrame. iSplits; ss. iCombine "A" "INV" as "A". iCombine "A" "FR" as "A".
          iCombine "A" "A2" as "A". iApply "A". }
        fold wf. steps. stb_tac; ss; clarify. steps.

        (*** calling App.init ***)
        hcall _ _ _.
        { iDestruct "FR" as "[[[A B] C] D]".
          iDestruct "B" as "[B|B]".
          { iDestruct "B" as (f h map lst0) "[[[E %] %] %]". ss. }
          iDestruct "B" as "[B|B]"; cycle 1.
          { iDestruct "B" as (f) "[[E %] %]". ss. }
          iDestruct "B" as "[% %]". iDestruct "P" as "[% %]". clarify. des; clarify.
          iModIntro. iSplitL "C D".
          - instantiate (4:=True%I). iSplitR; ss. iLeft. iSplits; ss; et; iFrame.
            + iSplits; ss.
            + iSplits; ss.
          - iFrame. iSplits; ss.
        }
        mCombine "A" "INIT". mOwnWf "A". exfalso. admit "ez".
      }
        harg_tgt.
        { iFrame. iSplits; ss; et. iCombine "A" "INIT" as "A". iAssumption. }
        fold wf.
        { steps. rewrite _UNWRAPU; ss. steps.
      - (* UNINIT *)
        hAPC _.
        { iIntros "[A B]". }
      steps.
    }
    econs; ss. init. harg. mDesAll.
    des; clarify. unfold gF, ccallU. steps. astart 10.
    des_ifs.
    - steps. acatch. hcall _ _ _ with "*"; auto.
      { iModIntro. iFrame. iSplits; try by (iPureIntro; refl).
        2: { iPureIntro. do 3 f_equal. instantiate (1:=x - 1). lia. }
        { ss. }
        { iPureIntro. lia. }
      }
      { esplits; ss; et. eapply OrdArith.lt_from_nat. lia. }
      steps. astop. ss. steps. mDesAll; clarify. rewrite Any.upcast_downcast. ss. steps.
      mAssert _ with "A INV1".
      { iCombine "A" "INV1" as "A". iApply (OwnM_Upd with "A").
        instantiate (1:=@URA.add IRA.t (IRA.client false) (IRA.module false)). r. ur. i. des_ifs. }
      force_l. eexists. steps. hret _; ss.
      { iMod "A1". iModIntro. iDestruct "A1" as "[B C]". iFrame. iSplits; ss; et. iPureIntro. do 2 f_equal. lia. }
    - steps.
      mAssertPure False.
      { iCombine "A" "INV" as "A". iOwnWf "A". ur in H0. des_ifs. }
      ss.
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
