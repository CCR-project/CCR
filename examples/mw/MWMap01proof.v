Require Import MWMap0 MWMap1 HoareDef SimModSem.
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
Require Import MWHeader Mem1 STB.

Set Implicit Arguments.

Local Open Scope nat_scope.




Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG mapRA Σ}.

  Let W: Type := Any.t * Any.t.

  (* Definition transl2 (hkvs: gmap mblock (list (Z * Z))): _mapRA := *)
  (*   fun h => *)
  (*     match hkvs !! h with *)
  (*     | Some kvs => Some (fun k => alist_find k kvs) *)
  (*     | _ => ε *)
  (*     end *)
  (* . *)

  (* Definition transl (hkvs: list (mblock * (list (Z * Z)))): _mapRA := *)
  (*   fun h => *)
  (*     match alist_find h hkvs with *)
  (*     | Some kvs => Some (fun k => alist_find k kvs) *)
  (*     | _ => ε *)
  (*     end *)
  (* . *)

(*   Definition transl (hkvs: list (mblock * (list (Z * Z)))): _mapRA. *)
(*     intros h. cbn. *)
(*     destruct (alist_find h hkvs) eqn:T. *)
(*     - apply Excl.just. intro k. *)
(*       destruct (alist_find k l) eqn:U. *)
(*       + apply (Some z). *)
(*       + apply None. *)
(*     - apply Excl.unit. *)
(*   Defined. *)
(* transl =  *)
(* λ (hkvs : list (nat * list (Z * Z))) (h : nat), *)
(*   let o := alist_find h hkvs in *)
(*   let T : alist_find h hkvs = o := eq_refl in *)
(*   match o as o0 return (alist_find h hkvs = o0 → Excl.car) with *)
(*   | Some l => *)
(*       λ _ : alist_find h hkvs = Some l, *)
(*         Excl.just *)
(*           (λ k : Z, *)
(*              let o0 := alist_find k l in *)
(*              let U : alist_find k l = o0 := eq_refl in *)
(*              match o0 as o1 return (alist_find k l = o1 → option Z) with *)
(*              | Some z => λ _ : alist_find k l = Some z, Some z *)
(*              | None => λ _ : alist_find k l = None, None *)
(*              end U) *)
(*   | None => λ _ : alist_find h hkvs = None, Excl.unit *)
(*   end T *)

  Let wf: _ -> W -> Prop :=
    @mk_wf _ unit
           (fun _ _ _ => True%I)
  .
  (* True **  *)
  (* Inductive sim_loc: URA.car (t:=(Excl.t _)) -> option (list val) -> option (list val) -> Prop := *)
  (* | sim_loc_k stk0: sim_loc (Some stk0) None (Some stk0) *)
  (* | sim_loc_u stk0: sim_loc ε (Some stk0) (Some stk0) *)
  (* | sim_loc_absent: sim_loc ε None None *)
  (* . *)

  (* Notation sim res0 mgr_src0 mgr_tgt0 := *)
  (*   (∀ h, sim_loc ((res0: URA.car (t:=_stkRA)) h) *)
  (*                 ((mgr_src0: gmap mblock (list val)) !! h) ((mgr_tgt0: gmap mblock (list val)) !! h)). *)

  (* Let wf: _ -> W -> Prop := *)
  (*   @mk_wf _ unit *)
  (*          (fun _ _mgr_src0 _mgr_tgt0 => *)
  (*             (∃ mgr_src0 mgr_tgt0 (res0: URA.car (t:=_stkRA)), *)
  (*                 (⌜(<<SRC: _mgr_src0 = mgr_src0↑>>) /\ (<<TGT: _mgr_tgt0 = mgr_tgt0↑>>) /\ *)
  (*                  (<<SIM: sim res0 mgr_src0 mgr_tgt0>>)⌝) *)
  (*                 ∧ ({{"O": OwnM ((Auth.black res0): URA.car (t:=stkRA))}}) *)
  (*             )%I) *)
  (* . *)



  (* From iris.algebra Require Import big_op. *)
  (* From iris.bi Require Import big_op. *)

  (* Let wf: _ -> W -> Prop := *)
  (*   @mk_wf _ unit *)
  (*          (fun _ _stk_mgr0 _ => *)
  (*             ⌜True⌝ ** (∃ (stk_mgr0: gmap mblock (list val)), *)
  (*                        (⌜_stk_mgr0 = stk_mgr0↑⌝) ∧ *)
  (*                        ({{"SIM": ([∗ map] handle ↦ stk ∈ stk_mgr0, *)
  (*                                   (∃ hd, OwnM ((handle, 0%Z) |-> [hd]) ** is_list hd stk))}}) *)
  (*          )) *)
  (* . *)

  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk, stb_incl (to_stb (MapStb ++ MemStb)) (global_stb sk).

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

  (* Ltac acatch := *)
  (*   match goal with *)
  (*   | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn ?args) >>= _)) ] => *)
  (*     astep fn (tt↑) *)
  (*   end. *)
  Local Transparent is_map.

  Theorem correct: refines2 [MWMap0.Map] [MWMap1.Map global_stb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { esplits; et. ss. econs; et. eapply to_semantic. iIntros "H". ss. }

    econs; ss.
    { init. harg. mDesAll; des; clarify. fold wf.
      unfold newF, ccallU. steps. astart 2.
      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall _ (1) _ with "*".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps. force_r; ss. steps.
      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall _ (_, _, _) _ with "*".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps. astop. steps. force_l. esplits. steps.
      hret _; ss.
      { iModIntro. iSplits; ss; et. unfold is_map. iExists _, []. iFrame. iSplits; ss; et. }
    }

    econs; ss.
    { init. harg. mDesAll; des; clarify. fold wf.
      des_ifs_safe; ss. mDesAll; des; clarify.
      unfold updateF, ccallU. steps. astart 6.
      rename n into h.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall _ (3) _ with "".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      rewrite points_to_split in *. rewrite Z.add_0_l in *. erewrite points_to_split with (ofs:=1%Z) in *.
      mAssert _ with "A1".
      { iDestruct "A1" as "[A [B C]]".
        instantiate (1:=OwnM ((a, 0%Z) |-> [Vundef]) ** OwnM ((a, 1%Z) |-> [Vundef]) **
                             OwnM ((a, 2%Z) |-> [Vundef])). iFrame. }
      mDesAll.
      unfold is_map in ACC. mDesAll; des; clarify.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall _ (_, _, _) _ with "A4".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall _ (_, _, _) _ with "A2".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall _ (_, _, _) _ with "A3".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall _ (_, _, _) _ with "A1".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall _ (_, _, _) _ with "POST".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      astop. steps. force_l. esplits. steps.
      hret _; ss.
      { iModIntro. iSplits; ss; et. unfold is_map.
        rename a0 into hd. rename a into newhd. rename a2 into kvs. rename z0 into k. rename z into v.
        iExists (Vptr newhd 0), ((k,v) :: kvs). iFrame. iSplits; ss; et; cycle 1.
        { iPureIntro. extensionality b. rewrite eq_rel_dec_correct. des_ifs. }
        iSplits; ss; et. iFrame. iSplits; ss; et.
        erewrite points_to_split with (tl:=[Vint v; hd]).
        erewrite points_to_split with (tl:=[hd]). rewrite Z.add_0_l.
        iSplitL "POST1"; et.
        iSplitL "POST2"; et.
      }
    }

    econs; ss.
    { init. harg. mDesAll; des; clarify. fold wf.
      des_ifs_safe; ss. mDesAll; des; clarify.
      unfold accessF, ccallU. steps. astart 2.
      rename n into h. rename z0 into k. rename z into v.
      unfold is_map in ACC. mDesAll; des; clarify. rename a into hd. rename a0 into kvs.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall _ (_, _, _) _ with "A1".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      mAssertPure (exists hdb, hd = Vptr hdb 0%Z).
      { destruct kvs; ss. des_ifs_safe. iDes. iPureIntro. et. }
      des. subst.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall _ (_, _, _, _) _ with "A".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      astop. steps. force_l. esplits. steps.
      hret _; ss.
      { iModIntro. iSplits; ss; et. unfold is_map. iSplits; ss; et. iFrame. }
    }

    econs; ss.
    { init. harg. mDesAll; des; clarify. fold wf.
      des_ifs_safe; ss. mDesAll; des; clarify.
      unfold loopF, ccallU. steps. astart 4.
      rename n into h. rename z0 into k. rename z into v.
      destruct l; ss. des_ifs_safe. rewrite eq_rel_dec_correct in *. mDesAll; des; clarify.
      rewrite points_to_split in *. rewrite Z.add_0_l in *. erewrite points_to_split with (ofs:=1%Z) in *.
      mAssert _ with "A2".
      { iDestruct "A2" as "[A [B C]]".
        instantiate (1:=OwnM ((a, 0%Z) |-> [_]) ** OwnM ((a, 1%Z) |-> [_]) **
                             OwnM ((a, 2%Z) |-> [_])). iFrame. }
      mDesAll.
      des_ifs.
      - acatch.
        { eapply STBINCL. stb_tac; ss. }
        hcall _ (_, _, _) _ with "A".
        { iModIntro. iSplits; ss; et. }
        { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
        fold wf. mDesAll; des; clarify. steps.
        force_r.
        { admit "intrange". }
        steps.

        acatch.
        { eapply STBINCL. stb_tac; ss. }
        hcall _ (_, _, _) _ with "A3".
        { iModIntro. iSplits; ss; et. }
        { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
        fold wf. mDesAll; des; clarify. steps.

        astop. steps. force_l. esplits. steps.
        hret _; ss.
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et.
          erewrite points_to_split with (tl:=[Vint v; a0]). rewrite Z.add_0_l.
          erewrite points_to_split with (tl:=[a0]).
          iSplitL "POST"; iFrame.
          iSplitL "POST1"; iFrame.
        }
      - acatch.
        { eapply STBINCL. stb_tac; ss. }
        hcall _ (_, _, _) _ with "A".
        { iModIntro. iSplits; ss; et. }
        { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
        fold wf. mDesAll; des; clarify. steps.

        force_r.
        { admit "intrange". }
        steps.

        acatch.
        { eapply STBINCL. stb_tac; ss. }
        hcall _ (_, _, _) _ with "A2".
        { iModIntro. iSplits; ss; et. }
        { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
        fold wf. mDesAll; des; clarify. steps.

        mAssertPure (exists hdb, a0 = Vptr hdb 0%Z).
        { destruct l; ss. des_ifs_safe. iDes. iPureIntro. et. }
        des. subst.

        acatch.
        { eapply STBINCL. stb_tac; ss. }
        hcall _ (_, _, _, _) _ with "A1".
        { iModIntro. iSplits; ss; et. }
        { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
        fold wf. mDesAll; des; clarify. steps.
        acatch.
    }
        astop.
        acatch.
        { eapply STBINCL. stb_tac; ss. }
        hcall _ (_, _, _) _ with "A3".
        { iModIntro. iSplits; ss; et. }
        { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
        fold wf. mDesAll; des; clarify. steps.

      -
      unfold is_map in ACC. mDesAll; des; clarify. rename a into hd. rename a0 into kvs.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall _ (_, _, _) _ with "A1".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      mAssertPure (exists hdb, hd = Vptr hdb 0%Z).
      { destruct kvs; ss. des_ifs_safe. iDes. iPureIntro. et. }
      des. subst.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall _ (_, _, _, _) _ with "A".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      astop. steps. force_l. esplits. steps.
      hret _; ss.
      { iModIntro. iSplits; ss; et. unfold is_map. iSplits; ss; et. iFrame. }
    }


    rename a4 into hkvs. rename a2 into h.
      mAssertPure (hkvs !! h = None).
      { destruct (hkvs !! h) eqn:T; ss.
        (* Search big_opM. *)
        iDestruct (big_sepM_lookup with "INV") as "B"; et. iDes.
        iExFalso. iApply (points_to_disj with "B"); eauto.
      }
      mAssert ([∗ map] h↦kvs ∈ <[h:=[]]>hkvs, ∃ hd, OwnM((h,0%Z) |-> [hd]) ** is_map_internal hd kvs)%I
        with "POST INV".
      { iApply big_sepM_insert; ss. iFrame. ss. iSplits; ss; et. }
      mAssert (#=> (OwnM (Auth.black (transl2 (<[h:=[]]>hkvs))) ** OwnM (is_map h (λ _, None)))) with "A".
      { iPoseProof (OwnM_Upd with "A") as "A"; cycle 1.
        { iMod "A". iModIntro. instantiate (1:=_ ⋅ _). iDestruct "A" as "[A B]". iFrame. }
        rewrite URA.add_comm. unfold is_map.
        etrans.
        { eapply Auth.auth_alloc2. instantiate (1:=(_is_map h (λ _, None))).
          mOwnWf "A". eapply Auth.black_wf in WF0. des.
          clear - PURE WF0.
          ur. i. ur in WF0. specialize (WF0 k).
          destruct (dec k h).
          - subst. clear WF0. unfold transl2, _is_map. ur. des_ifs. unfold alist in *. congruence.
          - unfold _is_map. des_ifs. rewrite URA.unit_id. ss.
        }
        eapply URA.updatable_add; try refl.
        clear - PURE.
        erewrite f_equal; try refl. f_equal.
        ur. unfold transl2, _is_map. extensionality h0.
        destruct (dec h h0); subst.
        - des_ifs_safe. unfold alist. rewrite PURE. rewrite URA.unit_idl. rewrite lookup_insert. ss.
        - des_ifs_safe. unfold alist. rewrite URA.unit_id. rewrite lookup_insert_ne; ss.
      }
      mUpd "A2".
      hret _; ss.
      { iModIntro. iDestruct "A2" as "[A B]". iSplitL "A A1".
        - iExists _. iFrame.
        - iSplits; ss; et.
      }
    }


    -
          Set Printing All.
          unfold alist.
          rewrite list_lookup_insert.
          lookup_insert
            lookup_insert_is_Some
            lookup_insert_Some
        admit "".
        - refl.
        rewrite add_disj_insert; ss.
        { eapply (@pw_insert_wf); et.
          { eapply Auth.black_wf; et. }
          { ur; ss. }
        }
        specialize (WF1 h). destruct (res0 h) eqn:T; ss; et.
        { spc SIM. rewrite T in *. inv SIM. rewrite _GUARANTEE in *. ss. }
      }
      { }
      big_opM_insert_delete
      big_sepM_insert_delete
      big_opM_insert
      big_sepM_insert
      hret _; ss.
            iFrame. iSplits; ss; et.
        (*** TODO: iSplits; ss; et gives weird goal ***)
        (* Global Opaque Pure And Sepconj Own OwnM Ex. *)
        iSplitL; [|iSplits; ss; et]; cycle 1.
        iExists _. iFrame. }
        iSplits; ss; et. iFrame.
      kinit. harg. fold wf. mDesAll; des; subst. ss.
    }
      
      ss; et. iFrame. iLeft. iSplits; ss; et. }


    econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. econs; ss. eapply to_semantic. iIntros "H". iClear "H". iSplits; ss. }
  Qed.

  Theorem sim_modsem: ModSemPair.sim (MWMap1.MapSem global_stb) MWMap0.MapSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. econs; ss. eapply to_semantic. iIntros "H". iClear "H". iSplits; ss. }
    econs; ss.
    { unfold newF. kinit. harg. fold wf. mDesAll; des; subst. ss.
      unfold new_body. steps. unfold ccallN, ccallU, cfunN, cfunU. steps.

      astart 2. acatch. { eapply STBINCL. stb_tac; ss. } hcall _ (Some _) _ with "SIM"; ss; et.
      { iModIntro. iSplits; ss; et.
        { instantiate (1:=1%nat). ss. }
        { iPureIntro. unfold_modrange_64. ss. }
      }
      { ss. }
      Ltac post_call :=
        fold wf; clear_fast; mDesAll; des_safe; subst; try rewrite Any.upcast_downcast in *; clarify; renamer.
      post_call. rename a0 into handle.
      steps.
      force_r.
      { ss. }
      steps.

      acatch. { eapply STBINCL. stb_tac; ss. } hcall _ (Some (_, _, _)) _ with "SIM A"; ss; et.
      { iModIntro. iSplitL "SIM"; ss.
        { iSplits; ss; et. }
        { iSplits; ss; et. }
      }
      { ss. }
      post_call. steps.
      astop. steps.

      force_l. exists handle. steps.
      destruct (stk_mgr0 !! handle) eqn:T.
      { mAssertPure False; ss.
        (*** IEXPLOIT*) iDestruct (big_sepM_lookup_acc with "SIM") as "[B C]"; et. iDestruct "B" as (x) "[B D]".
        iApply (points_to_disj with "POST B"); et.
      }
      astop. steps. astop. steps. force_l; ss. steps. astop. steps.

      hret _; ss.
      { iModIntro. iSplits; ss; et. iApply big_sepM_insert; ss. iFrame; ss; et. }
      (*** ISPECIALIZE SYNTAX: iSpecialize ("A" $! _ _ H0). et. *)
    }
    econs; ss.
    { unfold popF. kinit. harg. fold wf. mDesAll; des; subst. ss.
      unfold pop_body, ccallU, cfunU.
      steps. astop. steps. astop. steps. astop. steps. astart 7.

      hide_k. destruct v; ss. des_ifs. clear_fast.
      renamer. rename n into handle. rename l into stk. rename _UNWRAPU into T.
      mAssert _ with "SIM".
      { iDestruct (big_sepM_delete with "SIM") as "[B C]"; et. (* big_sepM_lookup_acc *)
        instantiate (1:=_ ** _). iSplitL "B". { iExact "B". } iExact "C". }
      mDesAll; ss. rename a into hd. renamer.

      acatch. { eapply STBINCL. stb_tac; ss. } hcall _ (Some (_, _, _)) _ with "SIM A"; ss; et.
      { iModIntro. iSplitL "SIM"; ss; et. }
      { ss. }
      post_call. unhide_k. steps.
      hide_k.

      force_r.
      { mAssertPure _.
        { iClear "SIM". iClear "POST". iApply is_list_wf. iApply "A2". }
        des; clarify; et. des_ifs.
      }
      steps.

      destruct stk as [|x stk1]; ss.
      - mDesAll. subst.
        unhide_k. steps. hide_k.
        acatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "SIM POST"; ss.
        { iModIntro. iSplitL "SIM"; ss; [et|]. iSplits; ss. repeat iRight. et. }
        post_call. unhide_k. steps. astop. steps.
        force_r.
        { ss. }
        steps. astop. steps. astop. steps.

        hret _; ss. iModIntro. iSplits; ss; et.
        destruct (stk_mgr1 !! handle) eqn:U.
        { iExFalso. iDestruct (big_sepM_lookup_acc with "SIM") as "[B C]"; et. iDestruct "B" as (x) "[SIM B]".
          iApply (points_to_disj with "POST1 SIM"). }
        iApply big_sepM_insert; ss. iSplitR "SIM"; et.
      - mDesAll. subst. rename a into hd. rename a0 into tl. rewrite points_to_split in ACC. mDesOwn "A1".
        rewrite Z.add_0_l in *.
        unhide_k. steps. hide_k.

        acatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "SIM A1"; ss.
        { iModIntro. iSplitL "SIM"; ss. { et. } iSplits; ss; et. }
        post_call. unhide_k. steps.

        force_r.
        { ss. }
        steps.

        force_r.
        { ss. }
        steps.

        unfold scale_int. uo. steps.
        acatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "SIM POST1"; ss.
        { iModIntro. iSplitL "SIM"; ss; et. }
        post_call. steps.

        acatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "SIM A2"; ss.
        { iModIntro. iSplitL "SIM"; ss; et. }
        post_call. steps.

        acatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "SIM POST2"; ss.
        { iModIntro. iSplitL "SIM"; ss; et. }
        post_call. steps.

        acatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _)) _ with "SIM POST1"; ss.
        { iModIntro. iSplitL "SIM"; ss; et. }
        post_call. steps.

        acatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "SIM POST"; ss.
        { iModIntro. iSplitL "SIM"; ss; et. }
        post_call. steps.

        astop. steps. unfold pget. steps. renamer.

        destruct (stk_mgr1 !! handle) eqn:V.
        { mAssertPure False; ss. iDestruct (big_sepM_lookup_acc with "SIM") as "[B C]"; et.
          iDestruct "B" as (y) "[SIM B]".
          iApply (points_to_disj with "POST1 SIM"). }
        steps. astop. steps. astop. steps.

        hret _; ss.
        { iModIntro. iSplits; ss; et. iApply big_sepM_insert; ss. iFrame. iExists _; ss. iFrame. }
    }
    econs; ss.
    { unfold pushF. kinit. harg. fold wf. mDesAll; des; subst. ss.
      unfold push_body, ccallU, cfunU.
      steps. astop. steps. astop. steps. astop. steps. astart 7.

      hide_k. destruct v; ss. des_ifs. clear_tac.
      rename n into handle. renamer. rename l into stk. rename _UNWRAPU into T.
      mAssert _ with "SIM".
      { iDestruct (big_sepM_delete with "SIM") as "[B C]"; et. (* big_sepM_lookup_acc *)
        instantiate (1:=_ ** _). iSplitL "B". { iExact "B". } iExact "C". }
      mDesAll; ss. renamer. rename a into hd.

      acatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some _) _ with "SIM"; ss; et.
      { iModIntro. iSplitL "SIM"; et. iSplits; ss; et.
        { instantiate (1:=2). ss. }
        { iPureIntro. ss. }
      }
      post_call. rename a0 into node. unhide_k. steps.

      rewrite points_to_split in ACC. mDesOwn "A1". rewrite Z.add_0_l in *. clear_fast.

      unfold scale_int. uo. steps.

      force_r; ss. steps.

      acatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "A SIM"; ss; et.
      { iModIntro. iSplitL "SIM"; et. }
      post_call. steps.

      acatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "A1 SIM"; ss; et.
      { iModIntro. iSplitL "SIM"; et. }
      post_call. steps.

      acatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "A3 SIM"; ss; et.
      { iModIntro. iSplitL "SIM"; et. }
      post_call. steps.

      acatch. { eapply STBINCL. stb_tac; ss. } hcall (ord_pure 0) (Some (_, _, _)) _ with "POST SIM"; ss; et.
      { iModIntro. iSplitL "SIM"; et. }
      post_call. steps.

      astop. steps.

      destruct (stk_mgr1 !! handle) eqn:V.
      { mAssertPure False; ss. iDestruct (big_sepM_lookup_acc with "SIM") as "[B C]"; et.
        iDestruct "B" as (y) "[SIM B]". iApply (points_to_disj with "POST3 SIM"). }

      hret _; ss.
      { iModIntro. iSplits; ss; et.
        iApply big_sepM_insert; ss. iFrame. iExists _; ss. iFrame.
        iExists _, _. iFrame. iSplit; ss. erewrite points_to_split with (hd:=v0) (tl:=[hd]).
        iSplitL "POST1"; et.
      }
    }
  Unshelve.
    all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk, stb_incl (to_stb (StackStb ++ MemStb)) (global_stb sk).

  Theorem correct: refines2 [Stack0.Stack] [Stack1.Stack global_stb].
  Proof.
    eapply adequacy_local2. econs; ss. ii. eapply sim_modsem; ss.
  Qed.

End SIMMOD.
