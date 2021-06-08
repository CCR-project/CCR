Require Import NewStack2 NewStack3A HoareDef SimModSem.
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
Require Import TODOYJ.
Require Import HTactics Logic IPM.
Require Import OpenDef.
Require Import TODO.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

(*   Let wf: W -> Prop := *)
(*     @mk_wf _ unit *)
(*            (fun _ _ _stk_mgr0 => *)
(*               (∃ (stk_mgr0: gmap mblock (list Z)), *)
(*                   (⌜<<CAST: _stk_mgr0 = stk_mgr0↑>>⌝) ∧ *)
(*                   (OwnM (Auth.black ([∗ map] handle ↦ stk ∈ stk_mgr0, *)
(*                                      (_is_stack handle stk)))) *)
(*               )%I) *)
(*            (fun _ _ _ => ⌜True⌝%I) *)
(*   . *)
(*   (big_opM bi_sep (fun k x => P) m) *)
(* ([∗ map] handle ↦ stk ∈ stk_mgr0, *)
(*                              (∃ hd, OwnM ((handle, 0%Z) |-> [hd]) ** is_list hd (map Vint stk))) *)
  Let wf: W -> Prop :=
    @mk_wf _ unit
           (fun _ _ _stk_mgr0 =>
              (∃ (stk_mgr0: gmap mblock (list Z)) (stk_res0: URA.car (t:=_stkRA)),
                  (⌜(<<PHYS: _stk_mgr0 = stk_mgr0↑>>) /\
                   (<<SIM: forall h stk, stk_res0 h = Some stk <-> stk_mgr0 !! h = Some stk>>)⌝)
                  ∧ (OwnM ((Auth.black stk_res0): URA.car (t:=stkRA)))
              )%I)
           (fun _ _ _ => ⌜True⌝%I)
  .

  (* Lemma is_stack_nil *)
  (*       h *)
  (*   : *)
  (*     (is_stack h []) = ε *)
  (* . *)
  (* Proof. *)
  (*   unfold is_stack. ss. unfold Auth.white. f_equal. unfold _is_stack. extensionality _h. des_ifs. ss. *)
  (* Qed. *)



  Section AUX.
    Context {K: Type} `{M: URA.t}.
    Let RA := URA.pointwise K M.

    Lemma pw_extends (f0 f1: K -> M) (EXT: @URA.extends RA f0 f1): <<EXT: forall k, URA.extends (f0 k) (f1 k)>>.
    Proof. ii. r in EXT. des. subst. ur. ss. eexists; et. Qed.
    (* Lemma pw_unfold_wf (f: K -> M): (forall k, URA.wf (f k)) -> @URA.wf RA f. Proof. i. ss. Qed. *)

    (* Lemma empty_wf: forall k, URA.wf ((@URA.unit RA) k). *)
    (* Proof. ii; ss. eapply URA.wf_unit. Qed. *)

    (* Lemma update_wf: forall `{Dec K} (f: @URA.car RA) k v (WF: URA.wf f) (WF: URA.wf v), URA.wf (update f k v: (@URA.car RA)). *)
    (* Proof. ii. unfold update. des_ifs; ss. Qed. *)

    Lemma pw_wf: forall (f: @URA.car RA) (WF: URA.wf f), <<WF: forall k, URA.wf (f k)>>.
    Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

  End AUX.

  Theorem sim_modsem: ModSemPair.sim (NewStack3A.StackSem) (NewStack2.StackSem).
  Proof.
    econstructor 1 with (wf:=wf); ss; et; swap 2 3.
    { econs; ss.
      - eapply to_semantic; cycle 1. { admit "ez - wf". } iIntros "H". iExists _, _. iSplit; ss; et.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iPureIntro. ss.
    }
    econs; ss.
    { unfold NewStack2.new_body, cfun. init. harg. fold wf. mDesAll. des; clarify.
      apply Any.upcast_inj in PURE0. des; clarify. steps. rewrite Any.upcast_downcast in *. clarify. steps.
      astart 0. astop. steps. rewrite Any.upcast_downcast in *. clarify.
      rename g into stk_mgr0. rename x0 into h. rename a1 into stk_res0. force_l. exists (Vptr h 0). steps.
      mOwnWf "A".
      assert(WF1: forall k, stk_res0 k <> Excl.boom).
      { eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k). rewrite H0 in WF0.
        ur in WF0. ss. }

      hret _; ss.
      { iPoseProof (OwnM_Upd with "A") as "A".
        { eapply Auth.auth_alloc2. instantiate (1:=(_is_stack h [])).
          ur. i. specialize (WF1 k).
          destruct (dec k h).
          - subst. ur.
            destruct (stk_res0 h) eqn:T; ss.
            + erewrite SIM in T. clarify.
            + unfold _is_stack. des_ifs.
          - ur.
            destruct (stk_res0 k) eqn:T; ss.
            + unfold _is_stack. des_ifs.
            + unfold _is_stack. des_ifs.
        }
        iMod "A". iDestruct "A" as "[A B]". iModIntro. iSplitL "A"; et.
        iExists _, _. iSplit; ss; et. iSplit; ss; et. iPureIntro. ii.
        assert(B: stk_res0 h = Excl.unit).
        { destruct (stk_res0 h) eqn:T; ss.
          - rewrite SIM in T. rewrite T in *. ss.
          - exploit WF1; et; ss.
        }
        clear - SIM WF1 B.
        destruct (dec h h0).
        - subst. rewrite lookup_insert.
          ur. ur. unfold _is_stack. des_ifs_safe. ss. clarify. split; i; clarify.
        - rewrite lookup_insert_ne; ss.
          ur. ur. unfold _is_stack. des_ifs_safe. ss. erewrite <- SIM. split; i; des_ifs.
      }
    }
    econs; ss.
    { unfold NewStack2.pop_body, cfun. init. harg. fold wf. des_ifs_safe. mDesAll. des; clarify.
      apply Any.upcast_inj in PURE0. des; clarify. steps. rewrite Any.upcast_downcast in *. clarify. steps.
      astart 0. astop. steps. rewrite Any.upcast_downcast in *. clarify.
      rename g into stk_mgr0. rename n into h. rename a1 into stk_res0.
      mCombine "A1" "A".
      mOwnWf "A1".
      assert(A: forall k, URA.wf ((stk_res0 k): URA.car (t:=Excl.t _))).
      { eapply URA.wf_mon in WF0.
        eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k). ss. }
      assert(B: stk_res0 h = Some l).
      { dup WF0.
        eapply Auth.auth_included in WF0. des. unfold _is_stack in WF0. eapply pw_extends in WF0. des.
        spc WF0. des_ifs. ss. eapply Excl.extends in WF0; ss. }
      assert(C:=B). eapply SIM in C. rewrite C. steps.
      destruct l as [|x stk].
      - steps. force_l. esplits. steps. hret _; ss.
        iDestruct "A1" as "[A B]".
        iModIntro. iFrame. iSplit; ss; et.
      - steps. Auth.auth_update
      force_l. exists (Vptr h 0). steps.
      mOwnWf "A".
      assert(WF1: forall k, stk_res0 k <> Excl.boom).
      { ur in WF0. des. r in WF1. repeat ur in WF1. rewrite Seal.sealing_eq in WF1. hexploit (WF1); et. }

      hret _; ss.
      { iPoseProof (OwnM_Upd with "A") as "A".
        { eapply Auth.auth_alloc2. instantiate (1:=(_is_stack h [])).
          ur. i. specialize (WF1 k).
          destruct (dec k h).
          - subst. ur.
            destruct (stk_res0 h) eqn:T; ss.
            + erewrite SIM in T. clarify.
            + unfold _is_stack. des_ifs.
          - ur.
            destruct (stk_res0 k) eqn:T; ss.
            + unfold _is_stack. des_ifs.
            + unfold _is_stack. des_ifs.
        }
        iMod "A". iDestruct "A" as "[A B]". iModIntro. iSplitL "A"; et.
        iExists _, _. iSplit; ss; et. iSplit; ss; et. iPureIntro. ii.
        assert(B: stk_res0 h = Excl.unit).
        { destruct (stk_res0 h) eqn:T; ss.
          - rewrite SIM in T. rewrite T in *. ss.
          - exploit WF1; et; ss.
        }
        clear - SIM WF1 B.
        destruct (dec h h0).
        - subst. rewrite lookup_insert.
          ur. ur. unfold _is_stack. des_ifs_safe. ss. clarify. split; i; clarify.
        - rewrite lookup_insert_ne; ss.
          ur. ur. unfold _is_stack. des_ifs_safe. ss. erewrite <- SIM. split; i; des_ifs.
      }
    }

    split; i.

          spc SIM. specialize (SIM []).
          rewrite <- SIM. lookup rewrite fn_lookup_insert. ss.
          ur.
          { iPureIntro.
      }
      admit "mid - somehow".
    }
    admit "mid - somehow".
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Theorem correct: ModPair.sim (NewStack2.Stack) (KMod.to_src NewStack1.KStack).
  Proof.
    econs; ss.
    { ii. eapply adequacy_lift. eapply sim_modsem; ss. }
    ii; ss. repeat (Psimpl; econs; ss).
  Qed.

End SIMMOD.
