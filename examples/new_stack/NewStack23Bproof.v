Require Import NewStack2 NewStack3B HoareDef SimModSem.
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
Require Import OpenDef STB.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Notation sim stk_res0 stk_mgr0 :=
    (∀ h,
        (∃ P stk, <<SRC: (stk_res0: URA.car (t:=_stkRA)) h = Some (Ag.ag P)>> ∧
                         <<TGT: (stk_mgr0: gmap mblock (list val)) !! h = Some stk>> ∧ <<PR: Forall P stk>>) ∨
        (<<SRC: (stk_res0: URA.car (t:=_stkRA)) h = None>> ∧
                <<TGT: (stk_mgr0: gmap mblock (list val)) !! h = None>>)
    )
  .
(*   match (stk_res0: URA.car (t:=_stkRA)) h with *)
(*   | Some P => ∃ stk, <<TGT: (stk_mgr0: gmap mblock (list val)) !! h = Some stk>> ∧ <<PR: Forall P stk>> *)
(*   | None => <<TGT: (stk_mgr0: gmap mblock (list val)) !! h = None>> *)
(*   end) *)

  Let wf: _ -> W -> Prop :=
    @mk_wf _ unit
           (fun _ _ _stk_mgr0 =>
              (∃ stk_mgr0 (stk_res0: URA.car (t:=_stkRA)),
                  (⌜(<<PHYS: _stk_mgr0 = stk_mgr0↑>>) /\ (<<SIM: sim stk_res0 stk_mgr0>>)⌝)
                  ∧ ({{"O": OwnM ((Auth.black stk_res0): URA.car (t:=stkRA))}})
              )%I)
           (fun _ _ _ => ⌜True⌝%I)
  .

  Variable global_stb: gname -> option fspec.
  Hypothesis STBINCL: stb_incl (to_stb StackStb) global_stb.

  Lemma _is_stack_wf
        h stk
    :
      <<WF: URA.wf (_is_stack h stk)>>
  .
  Proof. ur. ur. i. unfold _is_stack. des_ifs; ur; ss. i; clarify. Qed.

  Lemma sim_update
        stk_res0
        stk_mgr0
        (SIM: sim stk_res0 stk_mgr0)
        (h: mblock) P (stk: (list val))
        (PR: Forall P stk)
    :
      <<SIM: sim (<[h:=Some (Ag.ag P)]>stk_res0) (<[h:=stk]> stk_mgr0)>>
  .
  Proof.
    ii.
    destruct (dec h h0).
    - subst. rewrite ! lookup_insert. unfold insert, fn_insert. des_ifs. ss. left. esplits; et.
    - rewrite lookup_insert_ne; ss. unfold insert, fn_insert. des_ifs.
  Qed.

  Lemma add_disj_insert
        (stk_res0: _stkRA) h P
        (DISJ: stk_res0 h = ε)
    :
        (stk_res0 ⋅ _is_stack h P) = <[h:=Some (Ag.ag P)]>stk_res0
  .
  Proof.
    unfold insert, fn_insert. extensionality b. ur. unfold _is_stack. des_ifs.
    - rewrite DISJ. rewrite URA.unit_idl. ss.
    - rewrite URA.unit_id. ss.
  Qed.

  Theorem sim_modsem: ModSemPair.sim (NewStack3B.StackSem global_stb) (NewStack2.StackSem).
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. econs; ss.
      - eapply to_semantic. iIntros "H". iExists _, _. iSplit; ss; et.
        iSplit; ss; et.
      - red. uipropall.
    }
    econs; ss.
    { unfold NewStack2.new_body, cfun. init. harg. fold wf. mDesAll. des; clarify.
      rewrite Any.upcast_downcast in *. steps. rewrite Any.upcast_downcast in *. clarify.
      astart 0. astop. steps.
      rename g into stk_mgr0. rename x0 into h. rename a0 into stk_res0. rename x into P. des_u.
      force_l. exists ((Vptr h 0)↑). steps.
      mOwnWf "O".
      (* assert(WF1: forall k, stk_res0 k <> Excl.boom). *)
      (* { eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k). *)
      (*   destruct (stk_res0 k); ss. ur in WF0; ss. } *)

      hret _; ss.
      { iPoseProof (OwnM_Upd with "O") as "O".
        { eapply Auth.auth_alloc2. instantiate (1:=(_is_stack h P)).
          rewrite add_disj_insert; ss.
          { eapply (@pw_insert_wf); et.
            { eapply Auth.black_wf; et. }
            { ur; ss. eapply Ag.wf. }
          }
          specialize (SIM h). des; clarify.
        }
        iMod "O". iDestruct "O" as "[A B]". iModIntro. iSplitL "A"; et.
        iExists _, _. iSplit; ss; et. iSplit; ss; et. iPureIntro. ii.
        assert(B: stk_res0 h = None).
        { destruct (stk_res0 h) eqn:T; ss. specialize (SIM h). des; clarify. }
        rewrite add_disj_insert; ss. eapply sim_update; et.
      }
    }
    econs; ss.
    { unfold NewStack2.pop_body, cfun. init. harg. fold wf. des_ifs_safe. mDesAll. des; clarify.
      rewrite Any.upcast_downcast in *. steps. rewrite Any.upcast_downcast in *. clarify.
      astart 1. steps.
      rename g into stk_mgr0. rename n into h. rename a0 into stk_res0.
      mCombine "O" "A".
      mOwnWf "O".
      (* assert(A: forall k, URA.wf ((stk_res0 k): URA.car (t:=Excl.t _))). *)
      (* { eapply URA.wf_mon in WF0. *)
      (*   eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k). ss. } *)
      assert(D: URA.wf ((stk_res0: @URA.car _stkRA) h)).
      { eapply URA.wf_mon in WF0. eapply Auth.black_wf in WF0. des. eapply pw_wf in WF0. ss. }
      assert(B: stk_res0 h = Some (Ag.ag P)).
      { dup WF0.
        eapply Auth.auth_included in WF0. des. unfold _is_stack in WF0. eapply pw_extends in WF0. des.
        spc WF0. des_ifs. eapply Opt.extends in WF0; ss. des; subst. eapply Ag.extends in EXT; subst; ss.
        rewrite WF0 in D. ur in D. ss. }
      hexploit (SIM h); et. intro T; des; [|by clarify]. rewrite B in *.
      apply some_injective in SRC. eapply (@Ag.ag_inj _ P P0) in SRC. subst. ss. steps.
      rewrite TGT. steps.
      destruct stk as [|x stk1].
      - astop. steps. force_l. esplits. steps. hret _; ss. iDestruct "O" as "[A B]". iModIntro. iFrame.
        repeat iSplit; ss; et.
      - steps.
        assert(SIM0: sim (stk_res0) (<[h:=stk1]> stk_mgr0)).
        { replace stk_res0 with (<[h:=Some (Ag.ag P0)]>stk_res0); cycle 1.
          { extensionality h0. unfold insert, fn_insert. des_ifs. }
          eapply sim_update; et. inv PR; ss.
        }

        mDesOwn "O".
        astop. steps. force_l. esplits. steps. hret _; ss.
        { iModIntro. iFrame; ss; et. iSplits; ss; et. iPureIntro. right. inv PR; ss. }
    }
    econs; ss.
    { unfold NewStack2.push_body, cfun. init. harg. fold wf. des_ifs_safe. mDesAll. des; clarify.
      rewrite Any.upcast_downcast in *. steps. rewrite Any.upcast_downcast in *. clarify.
      rename g into stk_mgr0. rename n into h. rename a1 into stk_res0. rename a into x.
      mCombine "O" "PRE".
      mOwnWf "O".
      assert(A: forall k, URA.wf ((stk_res0 k): URA.car (t:=Opt.t (Ag.t _)))).
      { eapply URA.wf_mon in WF0.
        eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k). apply WF0. }
      assert(B: stk_res0 h = Some (Ag.ag P)).
      { dup WF0.
        eapply Auth.auth_included in WF0. des. unfold _is_stack in WF0. eapply pw_extends in WF0. des.
        spc WF0. des_ifs. eapply Opt.extends in WF0; et. des; subst. ss.
        eapply Ag.extends in EXT; subst; et. eapply Opt.wf; ss; et. rewrite <- WF0; et. }
      hexploit (SIM h); et. intro T; des; [|by clarify]. rewrite B in *.
      apply some_injective in SRC. apply (@Ag.ag_inj _ P P0) in SRC. subst. ss. rewrite TGT. steps.
      astart 1. astop.
      assert(SIM0: sim (stk_res0) (<[h:=x :: stk]> stk_mgr0)).
      { replace stk_res0 with (<[h:=Some (Ag.ag P0)]>stk_res0); cycle 1.
        { extensionality h0. unfold insert, fn_insert. des_ifs. }
        eapply sim_update; et.
      }
      mDesOwn "O".
      steps. force_l. esplits. steps. hret _; ss.
      { iModIntro. iFrame; ss; et. }
    }
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk, stb_incl (to_stb StackStb) (global_stb sk).

  Theorem correct: ModPair.sim (NewStack3B.Stack global_stb) (NewStack2.Stack).
  Proof.
    econs; ss.
    { ii. eapply sim_modsem; ss. }
  Qed.

End SIMMOD.
