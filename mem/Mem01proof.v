Require Import Mem0 Mem1 HoareDef STB SimModSem.
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
(* Require Import TODOYJ. *)
Require Import HTactics ProofMode.

Set Implicit Arguments.

Local Open Scope nat_scope.



(*** black + delta --> new_black ***)
Definition add_delta_to_black `{M: URA.t} (b: Auth.t M) (w: Auth.t _): Auth.t _ :=
  match b, w with
  | Auth.excl e _, Auth.frag f1 => Auth.excl (e ⋅ f1) URA.unit
  | _, _ => Auth.boom
  end
.



(*** TODO: move to Coqlib ***)
Lemma repeat_nth_some
      X (x: X) sz ofs
      (IN: ofs < sz)
  :
    nth_error (repeat x sz) ofs = Some x
.
Proof.
  ginduction sz; ii; ss.
  - lia.
  - destruct ofs; ss. exploit IHsz; et. lia.
Qed.

Lemma repeat_nth_none
      X (x: X) sz ofs
      (IN: ~(ofs < sz))
  :
    nth_error (repeat x sz) ofs = None
.
Proof.
  generalize dependent ofs. induction sz; ii; ss.
  - destruct ofs; ss.
  - destruct ofs; ss. { lia. } hexploit (IHsz ofs); et. lia.
Qed.

Lemma repeat_nth
      X (x: X) sz ofs
  :
    nth_error (repeat x sz) ofs = if (ofs <? sz) then Some x else None
.
Proof.
  des_ifs.
  - eapply repeat_nth_some; et. apply_all_once Nat.ltb_lt. ss.
  - eapply repeat_nth_none; et. apply_all_once Nat.ltb_ge. lia.
Qed.



Ltac Ztac := all_once_fast ltac:(fun H => first[apply Z.leb_le in H|apply Z.ltb_lt in H|apply Z.leb_gt in H|apply Z.ltb_ge in H|idtac]).

Lemma _points_to_hit: forall b ofs v, (_points_to (b, ofs) [v] b ofs) = (Some v).
Proof. i. rewrite unfold_points_to. ss. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia. rewrite Z.sub_diag. ss. Qed.

Lemma _points_to_miss: forall b ofs b' ofs' (MISS: b <> b' \/ ofs <> ofs') v, (_points_to (b, ofs) [v] b' ofs') = ε.
Proof. i. rewrite unfold_points_to. ss. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia. Qed.

Lemma _points_to_disj: forall b0 ofs0 v0 b1 ofs1 v1,
    URA.wf (_points_to (b0, ofs0) [v0] ⋅ _points_to (b1, ofs1) [v1]) -> b0 <> b1 \/ ofs0 <> ofs1.
Proof.
  ii. do 2 ur in H. specialize (H b0 ofs0). rewrite _points_to_hit in H.
  rewrite unfold_points_to in H. ss. ur in H. des_ifs_safe. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia.
  assert(ofs0 = ofs1) by lia. subst. rewrite Z.sub_diag in *. ss.
Qed.

Lemma dec_true: forall X `{Dec X} (x0 x1: X), x0 = x1 -> ((dec x0 x1): bool) = true.
Proof. ii. subst. unfold dec. destruct H; ss. Qed.

Lemma dec_false: forall X `{Dec X} (x0 x1: X), x0 <> x1 -> ((dec x0 x1): bool) = false.
Proof. ii. subst. unfold dec. destruct H; ss. Qed.
(* Lemma local_update_same *)
(*       `{M: URA.t} *)
(*       x0 y0 x1 y1 *)
(*       (SAME: x0 ⋅ y0 = x1 ⋅ y1) *)
(*   : *)
(*     URA.local_update x0 y0 x1 y1 *)
(* . *)
(* Proof. *)
(*   r. ii. des. subst. esplits; et. *)
(*   - *)
(* Qed. *)


Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  (* Eval compute in (@RA.car (RA.excl Mem.t)). *)
  Eval compute in (@URA.car Mem1._memRA).
  Inductive sim_loc: URA.car (t:=(Excl.t _)) -> option val -> Prop :=
  | sim_loc_present v: sim_loc (Some v) (Some v)
  | sim_loc_absent: sim_loc ε None
  .
  Hint Constructors sim_loc: core.

  Let W: Type := Any.t * Any.t.
  (* Let wf: W -> Prop := *)
  (*   @mk_wf *)
  (*     _ *)
  (*     Mem.t *)
  (*     (fun mem_tgt _ mp_tgt => (∃ mem_src, (OwnM ((Auth.black mem_src): URA.car (t:=Mem1.memRA))) *)
  (*                                            ** *)
  (*                                            (⌜forall b ofs, sim_loc ((mem_tgt.(Mem.cnts)) b ofs) (mem_src b ofs)⌝) *)
  (*                                            ** *)
  (*                                            (⌜mp_tgt = mem_tgt↑ /\ forall b ofs v, mem_tgt.(Mem.cnts) b ofs = Some v -> <<NB: b < mem_tgt.(Mem.nb)>>⌝) *)
  (*                              )%I) *)
  (*     top4 *)
  (* . *)

  Definition mem_wf (m0: Mem.t): Prop :=
    forall b ofs v, m0.(Mem.cnts) b ofs = Some v -> <<NB: b < m0.(Mem.nb)>>
  .

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _ unit
      (fun _ _ _mem_tgt0 =>
         (∃ (mem_tgt0: Mem.t) (memk_src0: URA.car (t:=Mem1._memRA)),
             (⌜(<<TGT: _mem_tgt0 = mem_tgt0↑>>) /\
              (<<SIM: forall b ofs, sim_loc (memk_src0 b ofs) (mem_tgt0.(Mem.cnts) b ofs)>>) /\
              (<<WFTGT: mem_wf mem_tgt0>>)⌝) ∧ (*** TODO: put it inside Mem.t? ***)
             (OwnM ((Auth.black memk_src0): URA.car (t:=Mem1.memRA)))
         )%I)
  .

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.

  Ltac renamer :=
    let tmp := fresh "_tmp_" in

    match goal with
    | H: context[OwnM (Auth.black ?x)] |- _ =>
      rename x into tmp; let name := fresh "memk_src0" in rename tmp into name
    end;

    match goal with
    | |- gpaco7 _ _ _ _ _ _ _ _ _ _ ((?mp_tgt↑), _) =>

      repeat multimatch mp_tgt with
             | context[?g] =>
               match (type of g) with
               | Mem.t =>
                 rename g into tmp; let name := fresh "mem_tgt0" in rename tmp into name
               | _ => fail
               end
             end
    end
  .

  Theorem correct_modsem: forall sk, ModSemPair.sim (SModSem.to_tgt (to_stb []) (Mem1.SMemSem sk)) (Mem0.MemSem sk).
  Proof.
   econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
   { ss. }
    { ss. eexists. econs; ss. eapply to_semantic.
      iIntros "H". iSplits; ss; et.
      { iPureIntro. ii. unfold Mem.load_mem, initial_mem_mr.
        cbn. uo. des_ifs; et. econs; et. }
      { iPureIntro. ii. ss. uo. des_ifs.
        apply nth_error_Some. ii. clarify. }
    }





    econs; ss.
    { unfold allocF. init.
      harg. fold wf. steps. hide_k. rename x into sz.
      { mDesAll; ss. des; subst.
        des_ifs_safe (mDesAll; ss). des; subst. clarify. rewrite Any.upcast_downcast in *. clarify.
        steps. unhide_k. steps. des_ifs; clarify.
        2:{ bsimpl; des; ss; apply sumbool_to_bool_false in Heq; try lia. }
        steps. astart 0. astop.
        renamer.
        set (blk := mem_tgt0.(Mem.nb) + x).

        mAssert _ with "INV" as "INV".
        { iApply (OwnM_Upd with "INV").
          eapply Auth.auth_alloc2.
          instantiate (1:=(_points_to (blk, 0%Z) (repeat (Vundef) sz))).
          mOwnWf "INV".
          clear - WF0 WFTGT SIM.
          ss. do 2 ur. ii. rewrite unfold_points_to. des_ifs.
          - bsimpl. des. des_sumbool. subst. hexploit (SIM blk k0); et. intro T.
            inv T; eq_closure_tac.
            + exploit WFTGT; et. i; des. lia.
            + rewrite URA.unit_idl. Ztac. rewrite repeat_length in *. rewrite Z.sub_0_r. rewrite repeat_nth_some; [|lia]. ur. ss.
          - rewrite URA.unit_id. do 2 eapply lookup_wf. eapply Auth.black_wf; et.
        }
        mUpd "INV". mDesOwn "INV".

        force_l. eexists. steps. hret _; ss. iModIntro. iSplitR "A"; cycle 1.
        { iSplitL; ss. iExists _. iSplitR; ss. }
        iExists _, _. iSplitR; ss. iPureIntro. esplits; et.
        - i. destruct (mem_tgt0.(Mem.cnts) blk ofs) eqn:T.
          { exfalso. exploit WFTGT; et. i; des. lia. }
          ss. do 2 ur.
          exploit SIM; et. rewrite T. intro U. inv U. rewrite unfold_points_to. ss. rewrite repeat_length.
          destruct (dec b blk); subst; ss.
          * unfold update. des_ifs_safe. rewrite <- H1. rewrite URA.unit_idl.
            rewrite Z.sub_0_r. rewrite Z.add_0_l. des_ifs.
            { bsimpl. des. Ztac. rewrite repeat_nth_some; try lia. econs. }
          * rewrite URA.unit_id. unfold update. des_ifs.
        - clear - WFTGT. ii. ss. unfold update in *. des_ifs. exploit WFTGT; et. i; des. r. lia.
      }
    }





    econs; ss.
    { unfold freeF. init.
      harg. fold wf. steps. hide_k.
      { des_ifs_safe (mDesAll; ss). des; subst.
        des_ifs; mDesAll; ss. des; subst. clarify. rewrite Any.upcast_downcast in *. clarify.
        steps. unhide_k. steps. astart 0. astop.
        renamer. rename n into b. rename z into ofs.
        rename a into v. rename WF into SIMWF.
        mCombine "INV" "A". mOwnWf "INV".
        assert(HIT: memk_src0 b ofs = (Some v)).
        { clear - WF.
          dup WF. eapply Auth.auth_included in WF. des. eapply pw_extends in WF. eapply pw_extends in WF.
          spc WF. rewrite _points_to_hit in WF.
          eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
        }
        set (memk_src1 := fun _b _ofs => if dec _b b && dec _ofs ofs
                                         then (ε: URA.car (t:=Excl.t _)) else memk_src0 _b _ofs).
        assert(WF': URA.wf (memk_src1: URA.car (t:=Mem1._memRA))).
        { clear - WF. unfold memk_src1. do 2 ur. ii. eapply URA.wf_mon in WF. ur in WF. des.
          des_ifs; et.
          - rp; [eapply URA.wf_unit|ss].
          - do 2 eapply lookup_wf; et.
        }
        hexploit (SIM b ofs); et. rewrite HIT. intro B. inv B.
        force_r.
        { unfold Mem.free in *. des_ifs. }
        rename t into mem_tgt1.

        mAssert _ with "INV" as "INV".
        { iApply (OwnM_Upd with "INV").
          Local Transparent points_to.
          eapply Auth.auth_dealloc.
          instantiate (1:=memk_src1).
          clear - WF'.

          r. i. rewrite URA.unit_idl.
          Local Opaque Mem1._memRA.
          ss. destruct H; clear H. (*** coq bug; des infloops ***) des. clarify.
          esplits; et.
          Local Transparent Mem1._memRA.
          unfold memk_src1. ss.
          apply func_ext. intro _b. apply func_ext. intro _ofs.
          des_ifs.
          - bsimpl; des; des_sumbool; subst.
            subst memk_src1. do 2 ur in WF'. do 2 spc WF'. des_ifs; bsimpl; des; des_sumbool; ss.
            clear - H0.
            do 2 ur in H0.
            specialize (H0 b ofs). rewrite _points_to_hit in H0. eapply Excl.wf in H0. des; ss.
          - rewrite unfold_points_to in *. do 2 ur. do 2 ur in H0.
            bsimpl. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia; try rewrite URA.unit_idl; try refl.
        }
        mUpd "INV".
        steps. force_l. eexists. steps. hret _; ss. iModIntro. iSplitL; cycle 1.
        { iPureIntro. ss. }
        iExists _, _. iSplitR "INV"; et. iPureIntro. esplits; ss; et.
        - { i. unfold Mem.free in _UNWRAPU. des_ifs. ss.
            subst memk_src1. ss.
            destruct (classic (b = b0 /\ ofs = ofs0)); des; clarify.
            - unfold update. des_ifs.
            - des_ifs.
              { Psimpl. bsimpl; des; des_sumbool; ss; clarify. }
              replace (update (Mem.cnts mem_tgt0) b (update (Mem.cnts mem_tgt0 b) ofs None) b0 ofs0) with
                  (Mem.cnts mem_tgt0 b0 ofs0); cycle 1.
              { unfold update. des_ifs. Psimpl. des_ifs; bsimpl; des; des_sumbool; ss; clarify. }
              et.
          }
        - clear - _UNWRAPU WFTGT. ii. unfold Mem.free in *. des_ifs. ss.
          unfold update in *. des_ifs; eapply WFTGT; et.
      }
    }





    econs; ss.
    { unfold loadF. init.
      harg. fold wf. steps. hide_k.
      { des_ifs_safe (mDesAll; ss). des; subst. clarify. rewrite Any.upcast_downcast in *. clarify.
        steps. unhide_k. steps. astart 0. astop.
        renamer. rename n into b. rename z into ofs.
        rename WF into SIMWF.
        mCombine "INV" "A". mOwnWf "INV".
        assert(T: memk_src0 b ofs = (Some v)).
        { clear - WF.
          dup WF.
          eapply Auth.auth_included in WF. des.
          eapply pw_extends in WF. eapply pw_extends in WF. spc WF. rewrite _points_to_hit in WF. des; ss.
          eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
        }
        exploit SIM; et. intro U. rewrite T in U. inv U; ss. unfold Mem.load.
        mDesOwn "INV".
        force_r; ss. clarify. steps. force_l. esplits. steps.
        hret _; ss. iModIntro. iFrame. iSplitL; et.
      }
    }





    econs; ss.
    { unfold storeF. init.
      harg. fold wf. steps. hide_k.
      { des_ifs_safe (mDesAll; ss). des; subst. clarify. rewrite Any.upcast_downcast in *. clarify.
        steps. unhide_k. steps. astart 0. astop.
        renamer.
        rename n into b. rename z into ofs. rename v into v1.
        rename a into v0. rename WF into SIMWF.
        steps.
        mCombine "INV" "A". mOwnWf "INV".
        assert(T: memk_src0 b ofs = (Some v0)).
        { clear - WF.
          dup WF.
          eapply Auth.auth_included in WF. des.
          eapply pw_extends in WF. eapply pw_extends in WF. spc WF. rewrite _points_to_hit in WF.
          des; ss.
          eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
        }
        exploit SIM; et. intro U. rewrite T in U. inv U; ss. unfold Mem.store. des_ifs. steps.
        set (memk_src1 := fun _b _ofs => if dec _b b && dec _ofs ofs then (Some v1: URA.car (t:=Excl.t _)) else memk_src0 _b _ofs).
        assert(WF': URA.wf (memk_src1: URA.car (t:=Mem1._memRA))).
        { clear - WF. unfold memk_src1. do 2 ur. ii. eapply URA.wf_mon in WF. ur in WF. des.
          des_ifs; et.
          - bsimpl; des; des_sumbool; subst. ur; ss.
          - do 2 eapply lookup_wf; et.
        }
        mAssert _ with "INV" as "INV".
        { iApply (OwnM_Upd with "INV").
          eapply Auth.auth_update with (a':=memk_src1) (b':=_points_to (b, ofs) [v1]); et.
          clear - wf WF'. ii. des. subst. esplits; et.
          do 2 ur in WF'. do 2 spc WF'.
          subst memk_src1. ss. des_ifs; bsimpl; des; des_sumbool; ss.
          do 2 ur. do 2 (apply func_ext; i). des_ifs.
          - bsimpl; des; des_sumbool; subst. rewrite _points_to_hit.
            do 2 ur in WF. do 2 spc WF. rewrite _points_to_hit in WF. eapply Excl.wf in WF. rewrite WF. ur; ss.
          - bsimpl; des; des_sumbool; rewrite ! _points_to_miss; et.
        }
        mUpd "INV". mDesOwn "INV".

        mEval ltac:(fold (points_to (b,ofs) [v1])) in "A".
        force_l. eexists. steps.
        hret _; ss. iModIntro. iFrame. iSplitL; ss; et.
        iExists _, _. iSplitR "INV"; et. iPureIntro. esplits; ss; et.
        - ii. cbn. des_ifs.
          + bsimpl; des; des_sumbool; subst. do 2 spc SIM. rewrite T in *. inv SIM.
            unfold memk_src1. rewrite ! dec_true; ss. econs.
          + replace (memk_src1 b0 ofs0) with (memk_src0 b0 ofs0); et.
            unfold memk_src1. des_ifs; bsimpl; des; des_sumbool; clarify; ss.
        - ii. ss. des_ifs.
          + bsimpl; des; des_sumbool; subst. eapply WFTGT; et.
          + eapply WFTGT; et.
      }
    }





    econs; ss.
    { unfold cmpF. init.
      harg. fold wf. steps. hide_k.
      { des_ifs_safe (mDesAll; ss). des; subst. clarify.
        steps. unhide_k. steps. astart 0. astop.
        renamer.
        rename b into result. rename c into resource. rename WF into SIMWF.
        assert (VALIDPTR: forall b ofs v (WF: URA.wf ((Auth.black (memk_src0: URA.car (t:=Mem1._memRA))) ⋅ ((b, ofs) |-> [v]))),
                   Mem.valid_ptr mem_tgt0 b ofs = true).
        { clear - SIM. i. cut (memk_src0 b ofs = Some v).
          - i. unfold Mem.valid_ptr.
            specialize (SIM b ofs). rewrite H in *. inv SIM. ss.
          - clear - WF.
            dup WF.
            eapply Auth.auth_included in WF. des.
            eapply pw_extends in WF. eapply pw_extends in WF. spc WF. rewrite _points_to_hit in WF.
            des; ss.
            eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
        }
        steps.
        mCombine "INV" "A". mOwnWf "INV". Fail mDesOwn "INV". (*** TODO: BUG!! FIXME ***)

        mDesOr "PRE".
        { mDesAll; subst. rewrite Any.upcast_downcast in *. clarify. steps.
          erewrite VALIDPTR; et. ss. steps.
          force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et.
        }
        mDesOr "PRE".
        { mDesAll; subst. rewrite Any.upcast_downcast in *. clarify. steps.
          erewrite VALIDPTR; et. ss. steps.
          force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et.
        }
        mDesOr "PRE".
        { mDesAll; subst. rewrite Any.upcast_downcast in *. clarify. steps.
          erewrite VALIDPTR; et; cycle 1.
          { rewrite URA.add_assoc in WF. eapply URA.wf_mon in WF; et. }
          erewrite VALIDPTR; et; cycle 1.
          { erewrite URA.add_comm with (a5:=(a, a0) |-> [a1]) in WF.
            rewrite URA.add_assoc in WF. eapply URA.wf_mon in WF; et. }
          rewrite URA.add_comm in WF. eapply URA.wf_mon in WF. ur in WF; ss. steps.
          replace (dec a a2 && dec a0 a3 ) with false; cycle 1.
          { clear - WF.
            exploit _points_to_disj; et. intro NEQ. des; try (by rewrite dec_false; ss).
            erewrite dec_false with (x0:=a0); ss. rewrite andb_false_r; ss.
          }
          steps. force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et.
        }
        mDesOr "PRE".
        { mDesAll; subst. rewrite Any.upcast_downcast in *. clarify. steps.
          erewrite VALIDPTR; et. ss. steps. rewrite ! dec_true; ss. steps.
          force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et.
        }
        { mDesAll; subst. des; subst. rewrite Any.upcast_downcast in *. clarify. steps.
          force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et.
        }
      }
    }
  Unshelve.
    all: ss.
    all: try (by econs).
  Qed.

  Theorem correct: refines2 [Mem0.Mem] [Mem1.Mem].
  Proof.
    eapply adequacy_local2. econs; ss; et. i. eapply correct_modsem.
  Qed.

End SIMMODSEM.
