Require Import NewStackHeader NewStack2 NewStack3A HoareDef SimModSem.
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
Require Import TODO.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Inductive sim_loc: URA.car (t:=(Excl.t _)) -> option (list Z) -> option (list Z) -> Prop :=
  | sim_loc_k stk0: sim_loc (Some stk0) None (Some stk0)
  | sim_loc_u stk0: sim_loc ε (Some stk0) (Some stk0)
  | sim_loc_absent: sim_loc ε None None
  .

  Notation sim res0 mgr_src0 mgr_tgt0 :=
    (∀ h, sim_loc ((res0: URA.car (t:=_stkRA)) h)
                  ((mgr_src0: gmap mblock (list Z)) !! h) ((mgr_tgt0: gmap mblock (list Z)) !! h)).

  Let wf: W -> Prop :=
    @mk_wf _ unit
           (fun _ _mgr_src0 _mgr_tgt0 =>
              (∃ mgr_src0 mgr_tgt0 (res0: URA.car (t:=_stkRA)),
                  (⌜(<<SRC: _mgr_src0 = mgr_src0↑>>) /\ (<<TGT: _mgr_tgt0 = mgr_tgt0↑>>) /\
                   (<<SIM: sim res0 mgr_src0 mgr_tgt0>>)⌝)
                  ∧ ({{"O": OwnM ((Auth.black res0): URA.car (t:=stkRA))}})
              )%I)
           top4
  .

  Section AUX.
    Context {K: Type} `{M: URA.t}.
    Let RA := URA.pointwise K M.

    Lemma pw_extends (f0 f1: K -> M) (EXT: @URA.extends RA f0 f1): <<EXT: forall k, URA.extends (f0 k) (f1 k)>>.
    Proof. ii. r in EXT. des. subst. ur. ss. eexists; et. Qed.

    Lemma pw_wf: forall (f: K -> M) (WF: URA.wf (f: @URA.car RA)), <<WF: forall k, URA.wf (f k)>>.
    Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

    Lemma pw_add_disj_wf
          (f g: K -> M)
          (WF0: URA.wf (f: @URA.car RA))
          (WF1: URA.wf (g: @URA.car RA))
          (DISJ: forall k, <<DISJ: f k = ε \/ g k = ε>>)
      :
        <<WF: URA.wf ((f: RA) ⋅ g)>>
    .
    Proof.
      ii; ss. ur. i. ur in WF0. ur in WF1. spc DISJ. des; rewrite DISJ.
      - rewrite URA.unit_idl; et.
      - rewrite URA.unit_id; et.
    Qed.

    Lemma pw_insert_wf: forall `{EqDecision K} (f: K -> M) k v (WF: URA.wf (f: @URA.car RA)) (WFV: URA.wf v),
        <<WF: URA.wf (<[k:=v]> f: @URA.car RA)>>.
    Proof.
      i. unfold insert, fn_insert. ur. ii. des_ifs. ur in WF. eapply WF.
    Qed.

  End AUX.

  Variable global_stb: list (string * fspec).
  Hypothesis STBINCL: stb_incl (DebugStb ++ StackStb) global_stb.

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
        (h: mblock) (stk: (list Z))
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
        (h: mblock) (stk: (list Z))
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
        (h: mblock) (stk: (list Z))
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
        (h: mblock) (stk: (list Z))
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
  (*   | [mp_src: gmap nat (list Z) |- _ ] => *)
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
    | |- gpaco6 _ _ _ _ _ _ _ _ (?mr_src, (?mp_src↑), _, _) (?mr_tgt, (?mp_tgt↑), _, _) =>

      (* rename mr_src into tmp; let name := fresh "res0" in rename tmp into name *)
      (* ; *)
      (* try match goal with *)
      (*     | H: _stkRA |- _ => rename H into tmp; let name := fresh "res0" in rename tmp into name *)
      (*     end *)
      (* ; *)

      repeat multimatch mp_src with
             | context[?g] =>
               match (type of g) with
               | gmap mblock (list Z) =>
                 rename g into tmp; let name := fresh "mgr_src0" in rename tmp into name
               | _ => fail
               end
             end
      ;

      repeat multimatch mp_tgt with
             | context[?g] =>
               match (type of g) with
               | gmap mblock (list Z) =>
                 rename g into tmp; let name := fresh "mgr_tgt0" in rename tmp into name
               | _ => fail
               end
             end
    end
  .
  Ltac post_call :=
    fold wf; clear_fast; mDesAll; des_safe; subst; try rewrite Any.upcast_downcast in *; clarify; renamer.

  Theorem sim_modsem: ModSemPair.sim (NewStack3A.StackSem global_stb) (NewStack2.StackSem).
  Proof.
    econstructor 1 with (wf:=wf); ss; et; swap 2 3.
    { econs; ss.
      - eapply to_semantic; cycle 1. { admit "ez - wf". } iIntros "H". iExists _, _, _. iSplits; ss; et.
        { iPureIntro. i. instantiate (1:=fun _ => Excl.unit). econs; ss; et. }
        { admit "ez - wf". }
    }
    econs; ss.
    { unfold NewStack2.new_body, cfun, cfun2. init. harg. post_call.
      destruct x; destruct (Any.split varg_src) eqn:X; des_ifs_safe; mDesAll; ss; des; subst.
      - rewrite Any.upcast_split. cbn. steps. rewrite Any.upcast_downcast in *. clarify. steps.
        rewrite Any.upcast_downcast in *. clarify.
        post_call.
        rename x into h.
        astart 0. astop. steps. force_l. exists (([]: list val)↑). steps.

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
      - unfold KModSem.transl_fun_tgt, new_body. rewrite X. cbn. steps. post_call.
        rename x into h. force_l. exists h. steps. rewrite Any.upcast_downcast. steps.
        assert(S:=SIM h). rewrite _GUARANTEE in *. inv S; ss. force_l; ss. steps.

        hret _; ss.
        iModIntro. iSplits; ss; et. iPureIntro. eapply sim_fresh_u; et.
    }

    econs; ss.
    { unfold NewStack2.pop_body, cfun, cfun2. init. harg. post_call.
      destruct x; destruct (Any.split varg_src) eqn:X; des_ifs_safe; mDesAll; ss; des; subst.
      - unfold KModSem.transl_fun_tgt. steps.
        rewrite Any.upcast_split. cbn. steps. rewrite Any.upcast_downcast in *. clarify. steps.
        rewrite Any.upcast_downcast in *. clarify. steps. renamer. rename n into h. rename a into stk0.

        mCombine "O" "A1".
        mOwnWf "O".
        assert(A: forall k, URA.wf ((res0 k): URA.car (t:=Excl.t _))).
        { eapply URA.wf_mon in WF0.
          eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k). ss. }
        assert(B: res0 h = Some stk0).
        { dup WF0.
          eapply Auth.auth_included in WF0. des. unfold _is_stack in WF0. eapply pw_extends in WF0. des.
          spc WF0. des_ifs. ss. eapply Excl.extends in WF0; ss. }
        assert(S:=SIM h). rewrite B in *. inv S; ss. steps.
        destruct stk0 as [|x stk1].
        + steps. hret _; ss. iDestruct "O" as "[A B]". iModIntro. iFrame. iSplitL "A"; ss; et.
          iSplits; ss; et. cbn. iSplits; ss; et.
        + steps.
          destruct (alist_find "debug" (DebugStb ++ StackStb)) eqn:U; cycle 1.
          { exfalso. stb_tac. ss. }
          dup U. revert U. stb_tac. clarify. i.
          apply STBINCL in U. rewrite U. steps.

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
            assert(D: ctx0 h = Excl.unit).
            { clear - B. repeat ur in B. unfold _is_stack in *. des_ifs. }
            extensionality h0. subst res1. unfold insert, fn_insert. des_ifs. 
            - ur. rewrite D. unfold _is_stack. ur. des_ifs.
            - unfold _is_stack. ur. des_ifs.
          }
          mUpd "A". mDesOwn "A".

          assert(SIM0: sim res1 mgr_src0 (<[h:=stk1]> mgr_tgt0)).
          { eapply sim_update_k; et. }

          hcall _ _ _ with "A"; ss; et.
          { iModIntro. iSplits; ss; et. }
          { ss. }
          steps. mDesAll. subst. des; clarify.

          hret _; ss.
          iModIntro. iFrame. iSplitL "O"; ss; et. iSplits; ss; et. cbn. iSplits; ss; et.
      - unfold KModSem.transl_fun_tgt, pop_body. rewrite X. cbn. steps. post_call. steps.
        rename n into h. rename l into stk0. destruct v; ss. des_ifs_safe.
        assert(S:=SIM h). rewrite _UNWRAPU0 in *. inv S; ss. steps.
        destruct stk0 as [|x stk1].
        + steps. hret _; ss. iModIntro. iSplits; ss; et.
        + steps.
          destruct (alist_find "debug" (DebugStb ++ StackStb)) eqn:U; cycle 1.
          { exfalso. stb_tac. ss. }
          dup U. revert U. stb_tac. clarify. i.
          apply STBINCL in U. rewrite U. steps.

          hcall _ _ _ with "-"; ss; et.
          { iModIntro. iSplits; ss; et. iPureIntro. eapply sim_update_u; et. }
          { ss. }
          post_call. steps.
          hret _; ss.
          { iModIntro. iSplits; ss; et. }
    }

    econs; ss.
    { unfold NewStack2.push_body, cfun, cfun2. init. harg. post_call.
      destruct x; destruct (Any.split varg_src) eqn:X; des_ifs_safe; mDesAll; ss; des; subst.
      - unfold KModSem.transl_fun_tgt. steps.
        rewrite Any.upcast_split. cbn. steps. rewrite Any.upcast_downcast in *. clarify. steps.
        rewrite Any.upcast_downcast in *. clarify. renamer. steps.
        rename n into h. rename l into stk0. rename z into x.
        mCombine "O" "A1".
        mOwnWf "O".
        assert(A: forall k, URA.wf ((res0 k): URA.car (t:=Excl.t _))).
        { eapply URA.wf_mon in WF0.
          eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k). ss. }
        assert(B: res0 h = Some stk0).
        { dup WF0.
          eapply Auth.auth_included in WF0. des. unfold _is_stack in WF0. eapply pw_extends in WF0. des.
          spc WF0. des_ifs. ss. eapply Excl.extends in WF0; ss. }
        assert(S:=SIM h). rewrite B in *. inv S; ss. steps.

        destruct (alist_find "debug" (DebugStb ++ StackStb)) eqn:U; cycle 1.
        { exfalso. stb_tac. ss. }
        dup U. revert U. stb_tac. clarify. i.
        apply STBINCL in U. rewrite U. steps.

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
          assert(D: ctx0 h = Excl.unit).
          { clear - B. repeat ur in B. unfold _is_stack in *. des_ifs. }
          extensionality h0. subst res1. unfold insert, fn_insert. des_ifs. 
          - ur. rewrite D. unfold _is_stack. ur. des_ifs.
          - unfold _is_stack. ur. des_ifs.
        }
        mUpd "A". mDesOwn "A".

        assert(SIM0: sim res1 mgr_src0 (<[h:=x::stk0]> mgr_tgt0)).
        { eapply sim_update_k; et. }

        hcall _ _ _ with "A"; ss; et.
        { iModIntro. iSplit; ss. iExists _, _, _. iSplits; ss; et. }
        { ss. }
        steps. mDesAll. subst. des; clarify.

        hret _; ss.
        iModIntro. iFrame. iSplitL "O"; ss; et.
      - unfold KModSem.transl_fun_tgt, push_body. rewrite X. cbn. steps. post_call. steps.
        rename n into h. rename l into stk0. destruct v; ss. des_ifs_safe.
        assert(S:=SIM h). rewrite _UNWRAPU in *. inv S; ss. steps.
        steps.
        destruct (alist_find "debug" (DebugStb ++ StackStb)) eqn:U; cycle 1.
        { exfalso. stb_tac. ss. }
        dup U. revert U. stb_tac. clarify. i.
        apply STBINCL in U. rewrite U. steps.

        hcall _ _ _ with "-"; ss; et.
        { iModIntro. iSplits; ss; et. iPureIntro. eapply sim_update_u; et. }
        { ss. }
        post_call. steps.
        hret _; ss.
        { iModIntro. iSplits; ss; et. }
    }
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Variable global_stb: Sk.t -> list (string * fspec).
  Hypothesis STBINCL: forall sk, stb_incl (DebugStb ++ StackStb) (global_stb sk).

  Theorem correct: ModPair.sim (NewStack3A.Stack global_stb) (NewStack2.Stack).
  Proof.
    econs; ss.
    { ii. eapply sim_modsem; ss. }
  Qed.

End SIMMOD.
