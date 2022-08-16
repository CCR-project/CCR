Require Import Stack2 Stack3A HoareDef SimModSem.
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
Require Import HTactics ProofMode IPM.
Require Import OpenDef STB.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Let W: Type := Any.t * Any.t.

  Inductive sim_loc: URA.car (t:=(Excl.t _)) -> option (list val) -> option (list val) -> Prop :=
  | sim_loc_k stk0: sim_loc (Some stk0) None (Some stk0)
  | sim_loc_u stk0: sim_loc ε (Some stk0) (Some stk0)
  | sim_loc_absent: sim_loc ε None None
  .

  Notation sim res0 mgr_src0 mgr_tgt0 :=
    (∀ h, sim_loc ((res0: URA.car (t:=_stkRA)) h)
                  ((mgr_src0: gmap mblock (list val)) !! h) ((mgr_tgt0: gmap mblock (list val)) !! h)).

  Let wf: _ -> W -> Prop :=
    @mk_wf _ unit
           (fun _ _mgr_src0 _mgr_tgt0 =>
              (∃ mgr_src0 mgr_tgt0 (res0: URA.car (t:=_stkRA)),
                  (⌜(<<SRC: _mgr_src0 = mgr_src0↑>>) /\ (<<TGT: _mgr_tgt0 = mgr_tgt0↑>>) /\
                   (<<SIM: sim res0 mgr_src0 mgr_tgt0>>)⌝)
                  ∧ ({{"O": OwnM ((Auth.black res0): URA.car (t:=stkRA))}})
              )%I)
  .

  Variable global_stb: gname -> option fspec.
  Hypothesis STBINCL: stb_incl (to_stb StackStb) global_stb.

  Lemma _is_stack_wf
        h stk
    :
      <<WF: URA.wf (_is_stack h stk)>>
  .
  Proof. ur. ur. i. unfold _is_stack. des_ifs; ur; ss. Qed.

  Hint Constructors sim_loc.
  Lemma sim_fresh_k
        res0 mgr_src0 mgr_tgt0
        (SIM: sim res0 mgr_src0 mgr_tgt0)
        (h: mblock) (stk: (list val))
        (FRESH: mgr_tgt0 !! h = None)
    :
      <<SIM: sim (<[h:=Excl.just stk]>res0) mgr_src0 (<[h:=stk]> mgr_tgt0)>>
  .
  Proof.
    ii.
    destruct (dec h h0).
    - subst. rewrite ! lookup_insert. unfold insert, fn_insert. des_ifs. ss.
      specialize (SIM h0). inv SIM; ss; et.
      { econs; ss; et. }
      { rewrite FRESH in *. clarify. }
      { econs; ss; et. }
    - rewrite lookup_insert_ne; ss. unfold insert, fn_insert. des_ifs.
  Qed.

  Lemma sim_update_k
        res0 mgr_src0 mgr_tgt0
        (SIM: sim res0 mgr_src0 mgr_tgt0)
        (h: mblock) (stk: (list val))
        (FRESH: mgr_src0 !! h = None)
    :
      <<SIM: sim (<[h:=Excl.just stk]>res0) mgr_src0 (<[h:=stk]> mgr_tgt0)>>
  .
  Proof.
    ii.
    destruct (dec h h0).
    - subst. rewrite ! lookup_insert. unfold insert, fn_insert. des_ifs. ss.
      specialize (SIM h0). inv SIM; ss; et.
      { econs; ss; et. }
      { rewrite FRESH in *. clarify. }
      { econs; ss; et. }
    - rewrite lookup_insert_ne; ss. unfold insert, fn_insert. des_ifs.
  Qed.

  Lemma sim_fresh_u
        res0 mgr_src0 mgr_tgt0
        (SIM: sim res0 mgr_src0 mgr_tgt0)
        (h: mblock) (stk: (list val))
        (FRESH: mgr_tgt0 !! h = None)
    :
      <<SIM: sim res0 (<[h:=stk]>mgr_src0) (<[h:=stk]> mgr_tgt0)>>
  .
  Proof.
    ii.
    destruct (dec h h0).
    - subst. rewrite ! lookup_insert. unfold insert, fn_insert. des_ifs. ss.
      specialize (SIM h0). inv SIM; ss; et.
      { rewrite FRESH in *. clarify. }
    - rewrite ! lookup_insert_ne; ss.
  Qed.

  Lemma sim_update_u
        res0 mgr_src0 mgr_tgt0
        (SIM: sim res0 mgr_src0 mgr_tgt0)
        (h: mblock) (stk: (list val))
        (FRESH: res0 h = ε)
    :
      <<SIM: sim res0 (<[h:=stk]> mgr_src0) (<[h:=stk]> mgr_tgt0)>>
  .
  Proof.
    ii.
    destruct (dec h h0).
    - subst. rewrite ! lookup_insert. unfold insert, fn_insert. des_ifs. ss.
      specialize (SIM h0). inv SIM; ss; et.
      { rewrite FRESH in *. clarify. }
    - rewrite ! lookup_insert_ne; ss.
  Qed.

  Lemma add_disj_insert
        (stk_res0: _stkRA) h stk
        (DISJ: stk_res0 h = ε)
    :
        (stk_res0 ⋅ _is_stack h stk) = <[h:=Excl.just stk]>stk_res0
  .
  Proof.
    unfold insert, fn_insert. extensionality b. ur. unfold _is_stack. des_ifs.
    - rewrite DISJ. rewrite URA.unit_idl. ss.
    - rewrite URA.unit_id. ss.
  Qed.

  (* Ltac renamer := *)
  (*   match goal with *)
  (*   | [mp_src: gmap nat (list val) |- _ ] => *)
  (*     let tmp := fresh "_tmp_" in *)
  (*     rename mp_src into tmp; *)
  (*     let name := fresh "stk_mgr0" in *)
  (*     rename tmp into name *)
  (*   end; *)
  (*   match goal with *)
  (*   | [ACC: current_iPropL _ ?Hns |- _ ] => *)
  (*     match Hns with *)
  (*     | context[(?name, ([∗ map] _↦_ ∈ _, _))%I] => mRename name into "SIM" *)
  (*     end *)
  (*   end *)
  (* . *)

  Ltac renamer :=
    let tmp := fresh "_tmp_" in

    match goal with
    | H: context[OwnM (Auth.black ?x)] |- _ =>
      rename x into tmp; let name := fresh "res0" in rename tmp into name
    end;

    match goal with
    | |- gpaco8 _ _ _ _ _ _ _ _ _ _ (Any.pair ?mp_src↑ _, _) ((?mp_tgt↑), _) =>

      (* rename mr_src into tmp; let name := fresh "res0" in rename tmp into name *)
      (* ; *)
      (* try match goal with *)
      (*     | H: _stkRA |- _ => rename H into tmp; let name := fresh "res0" in rename tmp into name *)
      (*     end *)
      (* ; *)

      repeat multimatch mp_src with
             | context[?g] =>
               match (type of g) with
               | gmap mblock (list val) =>
                 rename g into tmp; let name := fresh "mgr_src0" in rename tmp into name
               | _ => fail
               end
             end
      ;

      repeat multimatch mp_tgt with
             | context[?g] =>
               match (type of g) with
               | gmap mblock (list val) =>
                 rename g into tmp; let name := fresh "mgr_tgt0" in rename tmp into name
               | _ => fail
               end
             end
    end
  .
  Ltac post_call :=
    fold wf; clear_fast; mDesAll; des_safe; subst; try rewrite Any.upcast_downcast in *; clarify; renamer.

  Theorem sim_modsem: ModSemPair.sim (Stack3A.StackSem global_stb) (Stack2.StackSem).
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. econs; ss.
      - eapply to_semantic. iIntros "H". iExists _, _, _. iSplits; ss; et.
    }
    econs; ss.
    { unfold Stack2.new_body, cfunN, cfunU. init.
      - harg. mDesAll. des; clarify. steps.
        post_call.
        rename x0 into h.
        astart 0. astop. steps. force_l. eexists. steps.

        mOwnWf "O".
        assert(WF1: forall k, res0 k <> Excl.boom).
        { eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k).
          destruct (res0 k); ss. ur in WF0; ss. }

        hret _; ss.
        { iPoseProof (OwnM_Upd with "O") as "O".
          { eapply Auth.auth_alloc2. instantiate (1:=(_is_stack h [])).
            rewrite add_disj_insert; ss.
            { eapply (@pw_insert_wf); et.
              { eapply Auth.black_wf; et. }
              { ur; ss. }
            }
            specialize (WF1 h). destruct (res0 h) eqn:T; ss; et.
            { spc SIM. rewrite T in *. inv SIM. rewrite _GUARANTEE in *. ss. }
          }
          iMod "O". iDestruct "O" as "[A B]". iModIntro. iSplitL "A"; ss; et.
          iSplits; ss; et. iPureIntro. ii.
          assert(B: res0 h = Excl.unit).
          { destruct (res0 h) eqn:V; ss.
            - specialize (SIM h). rewrite V in SIM. inv SIM. rewrite _GUARANTEE in *. ss.
            - exploit WF1; et; ss.
          }
          rewrite add_disj_insert; ss. eapply sim_fresh_k; et.
        }
      - harg. mDesAll. des; clarify. unfold new_body. cbn. steps. astop. steps.
        rename x0 into h. force_l. exists h. steps.
        unfold pget. steps.
        assert(S:=SIM h). rewrite _GUARANTEE in *. inv S; ss. astop. steps.
        astop. steps. force_l; ss. steps. astop. steps.

        hret _; ss.
        iModIntro. iSplits; ss; et. iPureIntro. eapply sim_fresh_u; et.
    }

    econs; ss.
    { unfold Stack2.pop_body, cfunN. init.
      - harg. mDesAll. des; clarify. steps. ss. mDesAll. des; clarify.
        renamer. rename n into h. rename l into stk0.

        mCombine "O" "A".
        mOwnWf "O".
        assert(A: forall k, URA.wf ((res0 k): URA.car (t:=Excl.t _))).
        { eapply URA.wf_mon in WF0.
          eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k). ss. }
        assert(B: res0 h = Some stk0).
        { dup WF0.
          eapply Auth.auth_included in WF0. des. unfold _is_stack in WF0. eapply pw_extends in WF0. des.
          spc WF0. des_ifs. ss. eapply Excl.extends in WF0; ss. }
        assert(S:=SIM h). rewrite B in *. inv S; ss. steps.
        astart 0. astop.
        destruct stk0 as [|x stk1].
        + steps. force_l. esplits. steps.
          rewrite <- H3. steps. hret _; ss.
          iDestruct "O" as "[A B]". iModIntro. iFrame. iSplitL "A"; ss; et.
        + steps.

          set (res1:=<[h:=Excl.just stk1]>res0).
          assert(WF1: URA.wf (res1: URA.car (t:=_stkRA))).
          { subst res1. eapply (@pw_insert_wf); et.
            { eapply URA.wf_mon in WF0. eapply Auth.black_wf in WF0. ss. }
            ur; ss.
          }

          mAssert _ with "O".
          { iApply (OwnM_Upd with "O").
            eapply Auth.auth_update with (a':=res1) (b':=_is_stack h (stk1)).
            bar. ii. ss. des. clarify. esplits; et.
            assert(D: ctx h = Excl.unit).
            { clear - B. repeat ur in B. unfold _is_stack in *. des_ifs. }
            extensionality h0. subst res1. unfold insert, fn_insert. des_ifs.
            - ur. rewrite D. unfold _is_stack. ur. des_ifs.
            - unfold _is_stack. ur. des_ifs.
          }
          mUpd "A". mDesOwn "A".

          assert(SIM0: sim res1 mgr_src0 (<[h:=stk1]> mgr_tgt0)).
          { eapply sim_update_k; et. }

          force_l. esplits. steps.
          rewrite <- H3. steps. hret _; ss.
          iModIntro. iFrame. iSplitL "A"; ss; et.
      - harg. mDesAll. des; clarify. unfold pop_body. cbn.
        steps. astop. steps. astop. steps. astop. steps.
        rename n into h. rename l into stk0. destruct v; ss. des_ifs_safe.
        assert(S:=SIM h). rewrite _UNWRAPU1 in *. inv S; ss. steps.
        destruct stk0 as [|x0 stk1].
        + steps. hret _; ss. iModIntro. iSplits; ss; et.
        + steps. unfold pput. astop. steps.

          hret _; ss.
          { iModIntro. iSplits; ss; et. iPureIntro. eapply sim_update_u; et. }
    }

    econs; ss.
    { unfold Stack2.push_body, cfunN. init.
      - harg. mDesAll. des; clarify. steps. ss. mDesAll. des; clarify.
        renamer. rename n into h. rename l into stk0. rename v into x.
        mCombine "O" "A".
        mOwnWf "O".
        assert(A: forall k, URA.wf ((res0 k): URA.car (t:=Excl.t _))).
        { eapply URA.wf_mon in WF0.
          eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k). ss. }
        assert(B: res0 h = Some stk0).
        { dup WF0.
          eapply Auth.auth_included in WF0. des. unfold _is_stack in WF0. eapply pw_extends in WF0. des.
          spc WF0. des_ifs. ss. eapply Excl.extends in WF0; ss. }
        assert(S:=SIM h). rewrite B in *. inv S; ss. steps.

        set (res1:=<[h:=Excl.just (x::stk0)]>res0).
        assert(WF1: URA.wf (res1: URA.car (t:=_stkRA))).
        { subst res1. eapply (@pw_insert_wf); et.
          { eapply URA.wf_mon in WF0. eapply Auth.black_wf in WF0. ss. }
          ur; ss.
        }

        mAssert _ with "O".
        { iApply (OwnM_Upd with "O").
          eapply Auth.auth_update with (a':=res1) (b':=_is_stack h (x::stk0)).
          bar. ii. ss. des. clarify. esplits; et.
          assert(D: ctx h = Excl.unit).
          { clear - B. repeat ur in B. unfold _is_stack in *. des_ifs. }
          extensionality h0. subst res1. unfold insert, fn_insert. des_ifs.
          - ur. rewrite D. unfold _is_stack. ur. des_ifs.
          - unfold _is_stack. ur. des_ifs.
        }
        mUpd "A". mDesOwn "A".

        assert(SIM0: sim res1 mgr_src0 (<[h:=x::stk0]> mgr_tgt0)).
        { eapply sim_update_k; et. }

        astop. steps.
        force_l. esplits. steps.
        rewrite <- H3. steps. hret _; ss.
        iModIntro. iFrame. iSplitL "A"; ss; et.
      - harg. mDesAll. des; clarify. unfold push_body. cbn.
        steps. astop. steps. astop. steps. astop. steps. astop. steps.
        rename n into h. rename l into stk0. destruct v; ss. des_ifs_safe.
        assert(S:=SIM h). rewrite _UNWRAPU0 in *. inv S; ss. steps.
        unfold pput. steps.

        hret _; ss.
        { iModIntro. iSplits; ss; et. iPureIntro. eapply sim_update_u; et. }
    }
  Unshelve.
    all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk, stb_incl (to_stb StackStb) (global_stb sk).

  Theorem correct: refines2 [Stack2.Stack] [Stack3A.Stack global_stb].
  Proof.
    eapply adequacy_local2. econs; ss.
    { ii. eapply sim_modsem; ss. }
  Qed.

End SIMMOD.
