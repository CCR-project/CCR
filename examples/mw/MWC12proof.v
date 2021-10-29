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

Require Import HTactics2 ProofMode.
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
  Definition sim (f: Z -> option Z) (map: list (Z * Z)) (lst0: local_state): Prop :=
    (∀ k v (IN: f k = Some v),
        match lst0.(lst_cls) k with
        | uninit => False
        | opt => lst0.(lst_opt) k = Vint v
        | normal => alist_find k map = Some v
        end
    )
  .

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => (
           {{"INIT": ∃ f h map lst0, OwnM (mw_stateX f) ** OwnM (is_map h map)
                        ** ⌜st_src = (trans f)↑⌝ ** ⌜st_tgt = lst0↑⌝
                        ** ⌜lst0.(lst_map) = Vptr h 0%Z⌝ ** ⌜sim f map lst0⌝}} ∨
           {{"UNINIT": ⌜st_src = tt↑ ∧ st_tgt = tt↑⌝ ** OwnM (mw_stateX Maps.empty)
                                                  ** OwnM (mw_state Maps.empty)}}
         )%I)
  .

  Theorem correct: refines2 [MWC1.MW] [MWC2.MW].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss; cycle 1.
    { esplits. econs; et. eapply to_semantic. iIntros "[A B]".
      iSplitL; cycle 1.
      { iApply Own_unit; ss. }
      iRight. iSplits; ss; et. iFrame. iSplits; ss.
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

      unfold mainF, MWC2.mainF, ccallU.

      harg. fold wf.
      mDesAll; des; clarify.
      mDesOr "INVS"; mDesAll; des; clarify; steps.
      - (* INIT *)
        harg_tgt.
        { iFrame. iSplits; ss; et. iCombine "A" "INIT" as "A". iAssumption. }
        fold wf.
        { steps. rewrite _UNWRAPU; ss. steps.
      - (* UNINIT *)
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
