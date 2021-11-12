Require Import HoareDef MWHeader MWB0 MWC1 SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import Mem1.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import HTactics IPM ProofMode STB.

Set Implicit Arguments.

Local Open Scope nat_scope.





Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG spRA Σ}.

  Let W: Type := Any.t * Any.t.

(*   Definition trans (arr: val) (i v: Z): local_state := *)
(*     mk_lst (fun k => if dec k i then opt else normal *)
(* Record local_state : Set := mk_lst { lst_cls : Z → cls;  lst_opt : Z → val;  lst_map : val } *)

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
      (fun w0 mp_src mp_tgt =>
         ({{"UNINIT": OwnM sp_black ** ⌜(mp_src = tt↑) ∧ w0 = None ∧
                      ∃ (idv: option (val * val)) (map: val), mp_tgt = (idv, map)↑⌝}} ∨
          (* {{"INIT": OwnM sp_black ** ⌜w0 = None ∧ (∃ map i v cls, mp_tgt = (Some (Vint i, v), map)↑ *)
          (*                   ∧ mp_src = (mk_lst cls (fun k => if dec k i then v else Vundef) map)↑)⌝}} ∨ *)
          {{"INIT": OwnM sp_black ** ⌜w0 = None ∧ (∃ map idv cls, mp_tgt = (idv, map)↑
   (* ∧ match idv with *)
   (*   | Some (i, v) => mp_src = (mk_lst cls (fun k => if dec (Vint k) i then v else Vundef) map)↑ ∧ cls i = opt *)
   (*   | None => mp_src = (mk_lst cls (fun _ => Vundef) map)↑ *)
   (*   end)⌝}} ∨ *)
   ∧ ((idv = None ∧ mp_src = (mk_lst cls (fun _ => Vundef) map)↑) ∨
      (∃ i v, idv = Some (Vint i, v) ∧
              mp_src = (mk_lst cls (fun k => if dec k i then v else Vundef) map)↑ ∧ cls i = opt)))⌝}} ∨
          {{"LOCKED": OwnM sp_black ** OwnM sp_white ** ⌜w0 = Some (mp_src, mp_tgt)⌝}}
         )%I)
  .
     (* | Some (i, v) => mp_src = (mk_lst cls (fun k => if dec (Vint k) i then v else Vundef) map)↑ ∧ cls i = opt *)
     (* | None =>  *)

  Theorem correct: refines2 [MWB0.MW] [MWC1.MW].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=le); et; swap 2 3.
    { typeclasses eauto. }
    { esplits; et. econs; et. eapply to_semantic. iIntros "H". ss; et. iFrame. iLeft. iSplits; ss.
      iPureIntro. iSplits; ss; et. }

    econs; ss.
    { init. harg. fold wf. unfold mainF, MWB0.mainF, ccallU. mDesAll; des; clarify.
      mDesOr "INV"; ss; mDesAll; des; clarify.
      { steps. astop. steps.
        force_l; stb_tac; ss; clarify. steps.
        hcall _ _ (Some (_, _)) with "*".
        { iModIntro. iSplits; ss; et. iRight. iRight. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        steps.

        force_l; stb_tac; ss; clarify. steps.
        hcall _ _ None with "*".
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et.
          iPureIntro. eexists _, None, _; cbn. esplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.

        hcall _ _ None with "*".
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. steps.

        hret None; ss.
        { iModIntro. iSplits; ss; et.
          iDes; des; clarify.
          - iFrame; iSplits; ss; et. iLeft. iSplits; ss; et.
          - iFrame; iSplits; ss; et. iRight. iLeft. iSplits; ss; et. iPureIntro. esplits; ss; et.
          - iFrame; iSplits; ss; et. iRight. iLeft. iSplits; ss; et. iPureIntro. esplits; ss; et.
            right. esplits; ss; et.
        }
      }
      mDesOr "INV"; ss; cycle 1.
      { mDesAll; des; clarify.
        admit "ez".
      }
      { mDesAll; des_safe; clarify. steps. astop. steps.

        force_l; stb_tac; ss; clarify. steps.
        hcall _ _ None with "*".
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et.
          iPureIntro. des; clarify; iSplits; ss; et. left. iSplits; ss; et. f_equal. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.

        - 
      }
      mDesOr "INV"; ss; mDesAll; des; clarify.
      - steps. astop. steps.
        force_l; stb_tac; ss; clarify. steps.
        hcall _ _ (Some (_, _)) with "*".
        { iModIntro. iSplits; ss; et. iRight. iRight. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        steps.

        force_l; stb_tac; ss; clarify. steps.
        hcall _ _ None with "*".
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et.
          iPureIntro. eexists _, None, _; cbn. esplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.

        hcall _ _ None with "*".
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. steps.

        hret None; ss.
        { iModIntro. iSplits; ss; et.
          iDes; des; clarify.
          - iFrame; iSplits; ss; et. iLeft. iSplits; ss; et.
          - iFrame; iSplits; ss; et. iRight. iLeft. iSplits; ss; et. iPureIntro. esplits; ss; et.
          - iFrame; iSplits; ss; et. iRight. iLeft. iSplits; ss; et. iPureIntro. esplits; ss; et.
            right. esplits; ss; et.
        }
        { esplits; ss; et. }
    }
          -
          iSplits; ss; et.
          - iLeft. iSplits; ss; et.
          - iRight. iLeft. iSplits; ss; et. iPureIntro. esplits; ss; et.
          - iRight. iRight. iSplits; ss; et. iPureIntro. esplits; ss; et.
          -
          
        - }
        { 

        mDesOr "INV"; mDesAll; des; clarify; ss; cycle 1.
        { des_ifs.
          mDesOr "INV"; mDesAll; des; clarify; ss.
        }
        mDesOr "INV"; mDesAll; des; clarify; ss.
        steps.
        iPureIntro. left. esplits; et.
        hide_k. Set Printing All. rewrite Any.upcast_downcast.
      -
        des_u. steps. unfold mainF, MWC0.mainF, ccallU. steps. fold wf.
      mAssert (OwnM sp_black ** OwnM sp_white ** ⌜w = None ∧ ∃ (arr map: val), mp_tgt = (arr, map)↑⌝) with "*" as "A".
      { iDes; des; clarify; try (by iFrame; iSplits; ss; et). admit "ez". }
      mDesAll; des; clarify.
      astart 1. acatch. hcall _ 100 (Some (_, _)) with "*".
      { iModIntro. iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. steps. astop. mDesAll; des; clarify.
      mDesOr "INV"; mDesAll; des; clarify; ss.
      mDesOr "INV"; mDesAll; des; clarify; ss.
      steps. force_l; stb_tac; ss; clarify. steps.
      hcall _ _ _ with "-A".
      { iModIntro. iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify.
      mDesOr "INV"; mDesAll; des; clarify; ss.
      mDesOr "INV"; mDesAll; des; clarify; ss. steps.
      hcall _ _ _ with "*".
      { rewrite repeat_replicate. iDestruct (OwnM_replicate_sepL with "A") as "A". iMod "A".
        iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et.
        - iPureIntro. eapply sim_init.
      }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.

      hcall _ _ _ with "*".
      { iModIntro. iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. ss. des_ifs.
      hret None; ss.
      { iModIntro. iFrame. iSplits; ss; et. }
    }

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u.
      assert(w = None).
      { repeat mDesOr "INV"; mDesAll; des; clarify. mAssertPure False; ss. admit "ez". }
      steps. unfold loopF, MWC0.loopF, ccallU. steps. fold wf.
      force_l; stb_tac; ss; clarify. steps. hcall _ _ _ with "*".
      { iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps. hcall _ _ _ with "*".
      { iFrame. iSplits; ss; et. }
      { esplits; ss; et. }
      fold wf. mDesAll; des; clarify. steps. ss. des_ifs.
      hret None; ss.
      { iModIntro. iFrame; et. }
    }

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u. unfold putF, MWC0.putF, ccallU. steps. fold wf.
      force_r; ss. esplits; ss. steps.
      mDesOr "INV"; mDesAll; des; clarify.
      { exfalso. clear - _UNWRAPU0. apply Any.downcast_upcast in _UNWRAPU0. des.
        apply Any.upcast_inj in _UNWRAPU0. des; clarify.
        assert(T: exists (a b: local_state), a <> b).
        { exists (mk_lst (fun _ => uninit) (fun _ => Vundef) Vundef),
          (mk_lst (fun _ => uninit) (fun _ => Vundef) (Vint 1)). ii. clarify. }
        des. revert a b T. rewrite EQ. i. repeat des_u; ss.
      }
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { mAssertPure False; ss. admit "ez". }
      steps. rewrite Any.upcast_downcast in *. clarify. steps.
      destruct ((0 <=? z)%Z && (z <? 100)%Z) eqn:T.
      - inv PURE2. hexploit (SIM (Z.to_nat z)); [lia|]. rewrite ! Nat2Z.id in *;rewrite Z2Nat.id in *;try lia.
        intro U. des; ss.
        + rewrite INIT. ss. steps.
          mAssert _ with "A2".
          { iDestruct (big_sepL_insert_acc with "A2") as "[B C]"; et.
            instantiate (1:=_ ** _). iSplitL "B". { iExact "B". } iExact "C". }
          mDesAll; ss. rewrite Z2Nat.id in *; try lia. rewrite scale_int_8. steps.
          astart 1. acatch. hcall _ (_, _, _) (Some (_, _)) with "-A2".
          { iModIntro. iFrame. iSplitR "A1"; et. }
          { esplits; ss; et. }
          fold wf. mDesAll; des; clarify. ss. des_ifs.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          steps. astop. steps. hret None; ss.
          { iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et; cycle 1.
            { iApply "A2"; et. }
            iPureIntro. eapply sim_upd; et; try lia. econs; et.
          }
        + rewrite UNINIT. ss. steps. force_l. exists true. steps. unfold set; ss. des_ifs. steps.
          mAssert _ with "A2".
          { iDestruct (big_sepL_insert_acc with "A2") as "[B C]"; et.
            instantiate (1:=_ ** _). iSplitL "B". { iExact "B". } iExact "C". }
          mDesAll; ss. rewrite Z2Nat.id in *; try lia. rewrite scale_int_8. steps.
          astart 1. acatch. hcall _ (_, _, _) (Some (_, _)) with "-A2".
          { iModIntro. iFrame. iSplitR "A1"; et. }
          { esplits; ss; et. }
          fold wf. mDesAll; des; clarify. ss. des_ifs.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          steps. astop. steps. hret None; ss.
          { iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et; cycle 1.
            { iApply "A2"; et. }
            iPureIntro. eapply sim_upd2; et; try lia. econs; et.
          }
      - steps.
        destruct (lst_cls l z) eqn:U.
        + ss. steps. force_l. exists false. steps. unfold set. des_ifs. steps. force_l; stb_tac; ss; clarify.
          steps. hcall _ _ _ with "A INIT".
          { iModIntro. iSplits; ss; et. iRight. iRight. iFrame. iSplits; ss; et. }
          { esplits; ss; et. }
          fold wf. ss. des_ifs.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          steps. hret None; ss.
          { iSplits; ss; et. iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et.
            iPureIntro. eapply sim_upd3; et; try lia. }
        + exfalso. inv PURE2. hexploit (NORMAL z); et. { lia. } intro V. rewrite U in *; des; ss.
        + ss. steps. rewrite U. ss. steps. force_l; stb_tac; ss; clarify. steps.
          hcall _ _ _ with "-A2".
          { iModIntro. iSplits; ss; et. iRight. iRight. iFrame. iSplits; ss; et. }
          { esplits; ss; et. }
          fold wf. ss. des_ifs.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          steps. hret None; ss.
          { iSplits; ss; et. iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et. }
    }

    econs; ss.
    { init. harg. mDesAll. des; clarify. des_u. unfold getF, MWC0.getF, ccallU. steps. fold wf.
      force_r. esplits; ss. steps.
      mDesOr "INV"; mDesAll; des; clarify.
      { exfalso. clear - _UNWRAPU1. apply Any.downcast_upcast in _UNWRAPU1. des.
        apply Any.upcast_inj in _UNWRAPU1. des; clarify.
        assert(T: exists (a b: local_state), a <> b).
        { exists (mk_lst (fun _ => uninit) (fun _ => Vundef) Vundef),
          (mk_lst (fun _ => uninit) (fun _ => Vundef) (Vint 1)). ii. clarify. }
        des. revert a b T. rewrite EQ. i. repeat des_u; ss.
      }
      mDesOr "INV"; mDesAll; des; clarify; cycle 1.
      { mAssertPure False; ss. admit "ez". }
      steps. rewrite Any.upcast_downcast in *. clarify. steps.
      destruct ((0 <=? z)%Z && (z <? 100)%Z) eqn:T.
      - inv PURE2. hexploit (SIM (Z.to_nat z)); [lia|]. rewrite ! Nat2Z.id in *;rewrite Z2Nat.id in *;try lia.
        intro U. des; ss.
        + rewrite INIT. ss. steps.
          mAssert _ with "A2".
          { iDestruct (big_sepL_delete with "A2") as "[B C]"; et. xtra. }
          mDesAll; ss. rewrite Z2Nat.id in *; try lia. rewrite scale_int_8. steps.
          astart 1. acatch. hcall _ (_, _, _) (Some (_, _)) with "-A2".
          { iModIntro. iFrame. iSplits; ss; et. }
          { esplits; ss; et. }
          fold wf. mDesAll; des; clarify. ss. des_ifs.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          mDesOr "INV"; mDesAll; des; clarify; ss.
          steps. astop. steps. hret None; ss.
          { iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et; cycle 1.
            { iApply big_sepL_delete; et. rewrite Z2Nat.id. iFrame. lia. }
          }
      - steps. inv PURE2. exploit (NORMAL z); et. { lia. } intro U; des; clarify. rewrite U. ss.
        steps. force_l; stb_tac; ss; clarify. steps.
        hcall _ _ (Some (_, _)) with "-A2".
        { iModIntro. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. ss. des_ifs.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        steps. hret None; ss.
        { iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et. }
    }

  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
