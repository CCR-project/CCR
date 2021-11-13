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
          {{"INIT": OwnM sp_black ** ⌜w0 = None ∧
                    (∃ idv cls o map, mp_tgt = (idv, map)↑ ∧ mp_src = (mk_lst cls o map)↑ ∧
   (* ∧ match idv with *)
   (*   | Some (i, v) => mp_src = (mk_lst cls (fun k => if dec (Vint k) i then v else Vundef) map)↑ ∧ cls i = opt *)
   (*   | None => mp_src = (mk_lst cls (fun _ => Vundef) map)↑ *)
   (*   end)⌝}} ∨ *)
        ((idv = None ∧ (cls = fun _ => uninit) ∧ (o = fun _ => Vundef)) ∨
         (∃ i v, idv = Some (Vint i, v) ∧ cls i = opt ∧ (∀ j (NE: i <> j), cls j <> opt) ∧ o i = v)))⌝}} ∨
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
        hcall _ (Some (_, _)) with "*".
        { iModIntro. iSplits; ss; et. iRight. iRight. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        mDesOr "INV"; mDesAll; des; clarify; ss.
        steps.

        force_l; stb_tac; ss; clarify. steps.
        hcall _ None with "*".
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et.
          iPureIntro. eexists None. esplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify. steps. force_l; stb_tac; ss; clarify. steps.

        hcall _ None with "*".
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
        hcall _ (Some _) with "*".
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des_safe; clarify. steps. ss. des_ifs_safe.
        mDesOr "INV".
        { mDesAll; des; clarify; ss. }
        mDesOr "INV".
        { mDesAll; des; clarify; ss. }
        mDesAll; des_safe; clarify; ss.
        steps.

        force_l; stb_tac; ss; clarify. steps.
        hcall _ None with "*".
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et.
          iPureIntro. esplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des_safe; clarify. steps. ss. des_ifs_safe.

        force_l; stb_tac; ss; clarify. steps.
        hcall _ None with "*".
        { iModIntro. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des_safe; clarify. steps. ss. des_ifs_safe.
        clear PURE0.

        hret None; ss.
        { iModIntro. iSplits; ss; et. iDes; des_safe; clarify.
          - iFrame. iSplits; ss; et. iLeft. iPureIntro. esplits; ss; et.
          - iFrame. iSplits; ss; et. iRight. iLeft. iPureIntro. esplits; ss; et.
        }
      }
    }

    econs; ss.
    { init. harg. fold wf. unfold loopF, MWB0.loopF, ccallU. mDesAll; des; clarify.
      mDesOr "INV"; ss; mDesAll; des; clarify.
      { steps. force_l; stb_tac; ss; clarify. steps.
        hcall _ None with "*".
        { iModIntro. iFrame. iSplits; ss; et. iLeft. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify.
        steps.

        force_l; stb_tac; ss; clarify. steps.
        hcall _ None with "*".
        { iModIntro. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des; clarify.
        steps.

        hret None; ss.
        { iModIntro. iSplits; ss; et. iDes; des_safe; clarify.
          - iFrame. iSplits; ss; et. iLeft. iPureIntro. esplits; ss; et.
          - iFrame. iSplits; ss; et. iRight. iLeft. iPureIntro. esplits; ss; et.
        }
      }
      mDesOr "INV"; ss; mDesAll; des_safe; clarify.
      { steps. force_l; stb_tac; ss; clarify. steps.
        hcall _ None with "*".
        { iModIntro. iFrame. iSplits; ss; et. iRight. iLeft. iSplits; ss; et. iPureIntro. esplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des_safe; clarify.
        steps.

        force_l; stb_tac; ss; clarify. steps.
        hcall _ None with "*".
        { iModIntro. iFrame. iSplits; ss; et. }
        { esplits; ss; et. }
        fold wf. mDesAll; des_safe; clarify.
        steps.

        hret None; ss.
        { iModIntro. iSplits; ss; et. iDes; des_safe; clarify.
          - iFrame. iSplits; ss; et. iLeft. iPureIntro. esplits; ss; et.
          - iFrame. iSplits; ss; et. iRight. iLeft. iPureIntro. esplits; ss; et.
        }
      }
      { admit "ez". }
    }

    econs; ss.
    { init. harg. fold wf. unfold putF, MWB0.putF, ccallU. mDesAll; des; clarify.
      mDesOr "INV"; ss; mDesAll; des; clarify.
      { steps.
        exfalso. clear - _UNWRAPU0. apply Any.downcast_upcast in _UNWRAPU0. des.
        apply Any.upcast_inj in _UNWRAPU0. des; clarify.
        assert(T: exists (a b: local_state), a <> b).
        { exists (mk_lst (fun _ => uninit) (fun _ => Vundef) Vundef),
          (mk_lst (fun _ => uninit) (fun _ => Vundef) (Vint 1)). ii. clarify. }
        des. revert a b T. rewrite EQ. i. repeat des_u; ss.
      }
      mDesOr "INV"; ss; mDesAll; des_safe; clarify.
      { steps. force_r; esplits; ss. steps. des; clarify.
        - steps. unfold unint in *. des_ifs.
          steps. force_l. exists true. steps. unfold set. des_ifs. steps. astop. steps.
          hret None; ss.
          { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et.
            iRight; iLeft. iPureIntro. esplits; ss; et. right. esplits; ss; et; i; des_ifs. }
        - steps. unfold unint in *. des_ifs_safe.
          destruct (dec i z).
          + subst. des_ifs_safe. rewrite PURE1. steps. astop. steps.
            hret None; ss.
            { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et.
              iRight; iLeft. iPureIntro. esplits; ss; et. right. unfold set. esplits; ss; et; des_ifs. }
          + des_ifs_safe. steps. des_ifs.
            * steps. force_l. exists false. steps. unfold set. des_ifs. steps.
              force_l; stb_tac; ss; clarify. steps.
              hcall _ (Some _) with "*".
              { iModIntro. iFrame. iSplits; ss; et. }
              { esplits; ss; et. }
              fold wf. mDesAll; des; clarify.
              steps.

              ss. des_ifs_safe.
              mDesOr "INV"; ss; mDesAll; des; clarify.
              mDesOr "INV"; ss; mDesAll; des; clarify.

              hret None; ss.
              { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et.
                iRight; iLeft. iPureIntro. esplits; ss; et. right. esplits; ss; et; i; des_ifs; et. }
            * steps. des_ifs.
              { contradict PURE2; et. }
              steps.
              force_l; stb_tac; ss; clarify. steps.
              hcall _ (Some _) with "*".
              { iModIntro. iFrame. iSplits; ss; et. }
              { esplits; ss; et. }
              fold wf. mDesAll; des; clarify.
              mDesOr "INV"; ss; mDesAll; des; clarify.
              mDesOr "INV"; ss; mDesAll; des; clarify.
              steps.
              hret None; ss.
              { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et.
                iRight; iLeft. iPureIntro. esplits; ss; et. right. esplits; ss; et; i; des_ifs; et. }
      }
      { admit "ez". }
    }

    econs; ss.
    { init. harg. fold wf. unfold getF, MWB0.getF, ccallU. mDesAll; des; clarify.
      mDesOr "INV"; ss; mDesAll; des; clarify.
      { steps.
        exfalso. clear - _UNWRAPU1. apply Any.downcast_upcast in _UNWRAPU1. des.
        apply Any.upcast_inj in _UNWRAPU1. des; clarify.
        assert(T: exists (a b: local_state), a <> b).
        { exists (mk_lst (fun _ => uninit) (fun _ => Vundef) Vundef),
          (mk_lst (fun _ => uninit) (fun _ => Vundef) (Vint 1)). ii. clarify. }
        des. revert a b T. rewrite EQ. i. repeat des_u; ss.
      }
      mDesOr "INV"; ss; mDesAll; des_safe; clarify.
      { steps. force_r; esplits; ss. steps. des; clarify.
        destruct (dec i z); subst.
        - steps. astop. steps.
          hret None; ss.
          { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et.
            iRight; iLeft. iPureIntro. esplits; ss; et. right. esplits; ss; et; i; des_ifs. }
        - steps. des_ifs.
          { contradict PURE2; et. }
          steps.
          force_l; stb_tac; ss; clarify. steps.
          hcall _ (Some _) with "*".
          { iModIntro. iFrame. iSplits; ss; et. }
          { esplits; ss; et. }
          fold wf. mDesAll; des; clarify.
          mDesOr "INV"; ss; mDesAll; des; clarify.
          mDesOr "INV"; ss; mDesAll; des; clarify.
          steps.
          hret None; ss.
          { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et.
            iRight; iLeft. iPureIntro. esplits; ss; et. right. esplits; ss; et; i; des_ifs; et. }
      }
      { admit "ez". }
    }
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
