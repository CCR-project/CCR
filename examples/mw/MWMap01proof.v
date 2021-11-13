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
      hcall (1) _ with "*".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps. force_r; ss. steps.
      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall (_, _, _) _ with "*".
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
      hcall (3) _ with "".
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
      hcall (_, _, _) _ with "A4".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall (_, _, _) _ with "A2".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall (_, _, _) _ with "A3".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall (_, _, _) _ with "A1".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply OrdArith.lt_from_nat; lia. }
      fold wf. mDesAll; des; clarify. steps.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall (_, _, _) _ with "POST".
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
      hcall (_, _, _) _ with "A1".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. eapply Ord.omega_upperbound. }
      fold wf. mDesAll; des; clarify. steps.

      mAssertPure (exists hdb, hd = Vptr hdb 0%Z).
      { destruct kvs; ss. des_ifs_safe. iDes. iPureIntro. et. }
      des. subst.

      acatch.
      { eapply STBINCL. stb_tac; ss. }
      hcall (_, _, _, _) _ with "A".
      { iModIntro. iSplits; ss; et. }
      { esplits; ss; et. rewrite <- OrdArith.add_from_nat. eapply Ord.omega_upperbound. }
      fold wf. mDesAll; des; clarify. steps.

      astop. steps. force_l. esplits. steps.
      hret _; ss.
      { iModIntro. iSplits; ss; et. unfold is_map. iSplits; ss; et. iFrame. }
    }

    econs; ss.
    { init. harg. mDesAll; des; clarify. fold wf.
      des_ifs_safe; ss. mDesAll; des; clarify.
      unfold loopF, ccallU. steps. astart 3.
      rename n into h. rename z0 into k. rename z into v. rename l into kvs.
      destruct kvs; ss. des_ifs_safe. rewrite eq_rel_dec_correct in *. des_ifs; mDesAll; des; clarify.
      - rename a into cur. rename z into k. rename a0 into next.

        rewrite points_to_split in *. rewrite Z.add_0_l in *. erewrite points_to_split with (ofs:=1%Z) in *.
        mAssert _ with "A2".
        { iDestruct "A2" as "[A [B C]]".
          instantiate (1:=OwnM ((cur, 0%Z) |-> [_]) ** OwnM ((cur, 1%Z) |-> [_]) **
                               OwnM ((cur, 2%Z) |-> [_])). iFrame. }
        mDesAll.

        acatch.
        { eapply STBINCL. stb_tac; ss. }
        hcall (_, _, _) _ with "A".
        { iModIntro. iSplits; ss; et. }
        { esplits; ss; et. rewrite <- OrdArith.add_from_nat. eapply OrdArith.lt_from_nat; lia. }
        fold wf. mDesAll; des; clarify. steps.
        force_r.
        { admit "TODO: intrange". }
        steps.

        acatch.
        { eapply STBINCL. stb_tac; ss. }
        hcall (_, _, _) _ with "A3".
        { iModIntro. iSplits; ss; et. }
        { esplits; ss; et. rewrite <- OrdArith.add_from_nat. eapply OrdArith.lt_from_nat; lia. }
        fold wf. mDesAll; des; clarify. steps.

        astop. steps. force_l. esplits. steps.
        hret _; ss.
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et.
          erewrite points_to_split with (tl:=[_; _]).
          erewrite points_to_split with (tl:=[_]). rewrite Z.add_0_l.
          iSplitL "POST"; et.
          iSplitL "POST1"; et.
        }
      - rename a into cur. rename z into k0. rename a0 into next.

        rewrite points_to_split in *. rewrite Z.add_0_l in *. erewrite points_to_split with (ofs:=1%Z) in *.
        mAssert _ with "A2".
        { iDestruct "A2" as "[A [B C]]".
          instantiate (1:=OwnM ((cur, 0%Z) |-> [_]) ** OwnM ((cur, 1%Z) |-> [_]) **
                               OwnM ((cur, 2%Z) |-> [_])). iFrame. }
        mDesAll.

        acatch.
        { eapply STBINCL. stb_tac; ss. }
        hcall (_, _, _) _ with "A".
        { iModIntro. iSplits; ss; et. }
        { esplits; ss; et. rewrite <- OrdArith.add_from_nat. eapply OrdArith.lt_from_nat; lia. }
        fold wf. mDesAll; des; clarify. steps.
        force_r.
        { admit "TODO: intrange". }
        steps.

        acatch.
        { eapply STBINCL. stb_tac; ss. }
        hcall (_, _, _) _ with "A2".
        { iModIntro. iSplits; ss; et. }
        { esplits; ss; et. rewrite <- OrdArith.add_from_nat. eapply OrdArith.lt_from_nat; lia. }
        fold wf. mDesAll; des; clarify. steps.

        mAssertPure (exists nextb, next = Vptr nextb 0%Z).
        { destruct kvs; ss. des_ifs_safe. iDes. iPureIntro. et. }
        des. subst.

        acatch.
        { eapply STBINCL. stb_tac; ss. }
        hcall (_, _, _, _) _ with "A1".
        { iFrame. iSplits; ss; et. }
        { esplits; ss; et. rewrite <- ! OrdArith.add_from_nat. eapply OrdArith.lt_from_nat; lia. }
        fold wf. mDesAll; des; clarify. steps.

        astop. steps. force_l. esplits. steps.
        hret _; ss.
        { iModIntro. iSplits; ss; et. iFrame. iSplits; ss; et.
          erewrite points_to_split with (tl:=[_; _]).
          erewrite points_to_split with (tl:=[_]). rewrite Z.add_0_l.
          iSplitL "POST"; et.
          iSplitL "A3"; et.
        }
    }
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.

