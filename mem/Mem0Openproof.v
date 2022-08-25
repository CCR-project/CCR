Require Import Mem0 Mem1 MemOpen HoareDef SimModSem.
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
Require Import OpenDef HTactics ProofMode IPM.

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

  Let W: Type := Any.t * Any.t.
  (* Eval compute in (@RA.car (RA.excl Mem.t)). *)
  Eval compute in (@URA.car Mem1._memRA).

  (* Definition o_combine X (f: X -> X -> option X) (x0 x1: option X): option X := *)
  (*   match x0, x1 with *)
  (*   | Some x0, Some x1 => do x <- (f x0 x1); Some x *)
  (*   | Some x0, _ => Some x0 *)
  (*   | _, Some x1 => Some x1 *)
  (*   | _, _ => None *)
  (*   end *)
  (* . *)

  (* Definition o_xor X (x0 x1: option X): option X := *)
  (*   Eval red in (o_combine (fun _ _ => None) x0 x1) *)
  (* . *)

  (*** memk_src -> memu_src -> mem_tgt ***)
  Inductive sim_loc: URA.car (t:=(Excl.t _)) -> option val -> option val -> Prop :=
  | sim_loc_k v: sim_loc (Some v) None (Some v)
  | sim_loc_u v: sim_loc ε (Some v) (Some v)
  | sim_loc_absent: sim_loc ε None None
  .

  Definition mem_wf (m0: Mem.t): Prop :=
    forall b ofs v, m0.(Mem.cnts) b ofs = Some v -> <<NB: b < m0.(Mem.nb)>>
  .

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _ unit
      (fun _ _memu_src0 _mem_tgt0 =>
         (∃ (memu_src0: Mem.t) (mem_tgt0: Mem.t) (memk_src0: URA.car (t:=Mem1._memRA)),
             (⌜(<<SRC: _memu_src0 = memu_src0↑>>) /\ (<<TGT: _mem_tgt0 = mem_tgt0↑>>) /\
              (<<SIM: forall b ofs, sim_loc (memk_src0 b ofs) (memu_src0.(Mem.cnts) b ofs)
                                            (mem_tgt0.(Mem.cnts) b ofs)>>) /\
              (<<NB: memu_src0.(Mem.nb) <= mem_tgt0.(Mem.nb)>>) /\
              (<<WFSRC: mem_wf memu_src0>>) /\ (*** TODO: put it inside Mem.t? ***)
              (<<WFTGT: mem_wf mem_tgt0>>)⌝) ∧ (*** TODO: put it inside Mem.t? ***)
             (OwnM ((Auth.black memk_src0): URA.car (t:=Mem1.memRA)))
         )%I)
  .

  (***
Simulation Relation
where _ is physical (unknown src, tgt) and - is logical (known src)
src: __-_-_-
tgt: _______

Proof Outline
- alloc
  tgt allocates some dead blocks and then allocate the desired block.
  Such block is absent in both memk_src and memu_src. (by WF, SIM)
  + known
    Therefore, we can allocate new block in memk_src and still satisfy SIM.
  + unknown
    By SIMM, we know that memu_src.(nb) <= the new block.
    Therefore, we can allocate new block in memu_src and still satisfy SIM.
- free
  tgt frees some block.
  Either memk_src or memu_src should have that block, but not both.
  + known
    We know that memk_src has the block, and not memu.
    We have full tokens for the block so we can deallocate, thereby satisfying SIM (k/u both absent).
  + unknown
    We know that memu_src has the block, and not memk.
    We deallocate that block, thereby satisfying SIM (k/u both absent).
    SIMM holds. (should make lemma)
- access (load/store)
  tgt accesses some block.
  + known
    ...
  + unknown
    ...
   ***)

  Hint Resolve sim_itree_mon: paco.

  (* Opaque of_RA.t. *)
  (* Opaque URA.auth. *)
  (* Opaque URA.pointwise. *)
  Opaque URA.unit.

  Ltac renamer :=
    let tmp := fresh "_tmp_" in

    match goal with
    | H: context[OwnM (Auth.black ?x)] |- _ =>
      rename x into tmp; let name := fresh "memk_src0" in rename tmp into name
    end;

    match goal with
    | |- gpaco8 _ _  _ _ _ _ _ _ _ _ ((Any.pair ?mp_src↑ ?mr_src), _) ((?mp_tgt↑), _) =>

      (* rename mr_src into tmp; let name := fresh "res0" in rename tmp into name *)
      (* ; *)
      (* try match goal with *)
      (*     | H: _stkRA |- _ => rename H into tmp; let name := fresh "res0" in rename tmp into name *)
      (*     end *)
      (* ; *)

      repeat multimatch mp_src with
             | context[?g] =>
               match (type of g) with
               | Mem.t =>
                 rename g into tmp; let name := fresh "memu_src0" in rename tmp into name
               | _ => fail
               end
             end
      ;

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
  Ltac post_call :=
    fold wf; clear_fast; mDesAll; des_safe; subst; try rewrite Any.upcast_downcast in *; clarify; renamer.

  (* Ltac mRefresh := on_current ltac:(fun H => move H at bottom). *)

  Variable csl0 csl1: gname -> bool.
  Hypothesis EXCL: forall g, csl0 g -> csl1 g -> False.

  Theorem correct stb: refines2 [Mem0.Mem csl0] [MemOpen.Mem (fun g => csl0 g || csl1 g) csl1 stb].
  Proof.
    eapply adequacy_local2. econs; ss. i.
   econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
   { ss. }
   { ss. eexists. econs; ss. eapply to_semantic.
      iIntros "H". iSplits; ss; et.
      { iPureIntro. ii. unfold Mem.load_mem, initial_mem_mr.
        cbn. uo. des_ifs; et; try (by econs; et). exploit EXCL; et. i; ss. }
      { iPureIntro. ii. ss. uo. des_ifs.
        apply nth_error_Some. ii. clarify. }
      { iPureIntro. ii. ss. uo. des_ifs.
        apply nth_error_Some. ii. clarify. }
   }





    econs; ss.
    { unfold allocF. init.
      { harg. fold wf. steps. hide_k.
        destruct x as [sz|]; cycle 1.
        { mDesAll; des; clarify.
          (*** TODO: remove redundancy with u (context) case ***)
          (*** COPY START ***)
          mDesAll. des; subst. steps. destruct v; ss. clarify. unhide_k.
          steps.
          renamer. steps. des_ifs; steps.

          set (blk := mem_tgt0.(Mem.nb) + x). clarify. rename z into sz.
          force_l. exists (mem_tgt0.(Mem.nb) - memu_src0.(Mem.nb) + x). steps.
          unfold pput. steps.
          replace (Mem.nb memu_src0 + (Mem.nb mem_tgt0 - Mem.nb memu_src0 + x)) with (Mem.nb mem_tgt0 + x) by lia.
          hret _; ss. iModIntro. iSplitL "INV"; ss.
          iExists _, _, _. iSplitR; ss. iPureIntro. esplits; et; cbn.
          - ii.
            destruct (dec b blk); subst.
            { unfold update. des_ifs_safe.
              hexploit (SIM blk ofs); et. intro T.
              destruct (Mem.cnts mem_tgt0 blk ofs) eqn: U.
              { exploit (WFTGT blk ofs); et. i; des. lia. }
              inv T. des_ifs; econs; et.
            }
            unfold update. des_ifs.
          - ii. ss. unfold update in *. des_ifs. r. exploit WFSRC; et. i; des. lia.
          - ii. ss. unfold update in *. des_ifs. r. exploit WFTGT; et. i; des. lia.
          (*** COPY END ***)
        }
        mDesAll; ss. des; subst.
        des_ifs_safe (mDesAll; ss). des; subst. clarify.
        steps. unhide_k. steps. des_ifs; clarify.
        2:{ bsimpl; des; des_sumbool; ss; try lia. }
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
            + rewrite URA.unit_idl. Ztac. rewrite repeat_length in *. rewrite Z.sub_0_r. rewrite repeat_nth_some; [|lia]. ur. ss.
          - rewrite URA.unit_id. do 2 eapply lookup_wf. eapply Auth.black_wf; et.
        }
        mUpd "INV". mDesOwn "INV". steps.

        force_l. eexists. steps. hret _; ss. iModIntro. iSplitR "A"; cycle 1.
        { iSplits; ss; et. }
        iExists _, _, _. iSplitR; ss. iPureIntro. esplits; et.
        - i. destruct (mem_tgt0.(Mem.cnts) blk ofs) eqn:T.
          { exfalso. exploit WFTGT; et. i; des. lia. }
          ss. do 2 ur.
          exploit SIM; et. rewrite T. intro U. inv U. rewrite unfold_points_to. ss. rewrite repeat_length.
          destruct (dec b blk); subst; ss.
          * unfold update. des_ifs_safe. rewrite <- H1. rewrite <- H2. rewrite URA.unit_idl.
            rewrite Z.sub_0_r. rewrite Z.add_0_l. des_ifs.
            { bsimpl. des. Ztac. rewrite repeat_nth_some; try lia. econs. }
            { econs. }
          * rewrite URA.unit_id. unfold update. des_ifs.
        - cbn. lia.
        - clear - WFTGT. ii. ss. unfold update in *. des_ifs. exploit WFTGT; et. i; des. r. lia.
      }
      { harg. fold wf. steps. hide_k. destruct x.
        mDesAll. des; subst. rewrite _UNWRAPU. steps. destruct v; ss. clarify. unhide_k.
        steps. rewrite Any.upcast_downcast in *. clarify.
        renamer. steps. des_ifs; steps.

        set (blk := mem_tgt0.(Mem.nb) + x). clarify. rename z into sz.
        force_l. exists (mem_tgt0.(Mem.nb) - memu_src0.(Mem.nb) + x). steps.
        unfold pput. steps.
        replace (Mem.nb memu_src0 + (Mem.nb mem_tgt0 - Mem.nb memu_src0 + x)) with (Mem.nb mem_tgt0 + x) by lia.
        hret _; ss. iModIntro. iSplitL "INV"; ss.
        iExists _, _, _. iSplitR; ss. iPureIntro. esplits; et; cbn.
        - ii.
          destruct (dec b blk); subst.
          { unfold update. des_ifs_safe.
            hexploit (SIM blk ofs); et. intro T.
            destruct (Mem.cnts mem_tgt0 blk ofs) eqn: U.
            { exploit (WFTGT blk ofs); et. i; des. lia. }
            inv T. des_ifs; econs; et.
          }
          unfold update. des_ifs.
        - ii. ss. unfold update in *. des_ifs. r. exploit WFSRC; et. i; des. lia.
        - ii. ss. unfold update in *. des_ifs. r. exploit WFTGT; et. i; des. lia.
      }
    }





    econs; ss.
    { unfold freeF. init.
      { harg. fold wf. steps.
        destruct x as [[b ofs]|]; cycle 1.
        { mDesAll; des; clarify.
          (*** TODO: remove redundancy with u (context) case ***)
          (*** COPY START ***)
          des_ifs_safe (mDesAll; ss). des; subst.
          steps. destruct v; ss. clarify. steps.
          renamer.
          steps.
          rename n into b. rename z into ofs.
          force_r.
          { unfold Mem.free in *. des_ifs. hexploit (SIM b ofs); et. intro T.
            rewrite Heq in *. rewrite Heq0 in *. inv T.
          }
          rename t into mem_tgt1.
          steps.
          hret _; ss. iModIntro. iSplitL; ss.
          iExists _, _, _. iSplitR; ss. iPureIntro. esplits; et; cbn.
          - ii. unfold Mem.free in *. des_ifs. ss. unfold update. des_ifs.
            replace (memk_src0 b0 ofs0) with (@URA.unit (Excl.t val)); cycle 1.
            { hexploit (SIM b0 ofs0); et. intro T. rewrite Heq in *. rewrite Heq0 in *. inv T; ss. }
            econs.
          - unfold Mem.free in *. des_ifs.
          - rr in WFSRC. rr. ii. unfold Mem.free in *. des_ifs. ss. unfold update in *. des_ifs; et.
          - rr in WFTGT. rr. ii. unfold Mem.free in *. des_ifs. ss. unfold update in *. des_ifs; et.
          (*** COPY END ***)
        }
        hide_k.
        des_ifs_safe (mDesAll; ss). des; subst.
        des_ifs; mDesAll; ss. des; subst. clarify. rewrite Any.upcast_downcast in *. clarify.
        steps. unhide_k. steps. astart 0. astop.
        renamer.
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
        { iSplits; ss; et. }
        iExists _, _, _. iSplitR "INV"; et. iPureIntro. esplits; ss; et.
        - { i. unfold Mem.free in _UNWRAPU. des_ifs. ss.
            subst memk_src1. ss.
            destruct (classic (b = b0 /\ ofs = ofs0)); des; clarify.
            - unfold update. des_ifs. rewrite <- H2. econs.
            - des_ifs.
              { Psimpl. bsimpl; des; des_sumbool; ss; clarify. }
              replace (update (Mem.cnts mem_tgt0) b (update (Mem.cnts mem_tgt0 b) ofs None) b0 ofs0) with
                  (Mem.cnts mem_tgt0 b0 ofs0); cycle 1.
              { unfold update. des_ifs. Psimpl. des_ifs; bsimpl; des; des_sumbool; ss; clarify. }
              et.
          }
        - unfold Mem.free in *. des_ifs.
        - clear - _UNWRAPU WFTGT. ii. unfold Mem.free in *. des_ifs. ss.
          unfold update in *. des_ifs; eapply WFTGT; et.
      }
      { harg. fold wf. steps. destruct x.
        des_ifs_safe (mDesAll; ss). des; subst.
        steps. destruct v; ss. clarify. steps.
        rewrite Any.upcast_downcast in *. clarify. rewrite _UNWRAPU; ss.
        renamer.
        steps.
        rename n into b. rename z into ofs.
        force_r.
        { unfold Mem.free in *. des_ifs. hexploit (SIM b ofs); et. intro T.
          rewrite Heq0 in *. rewrite Heq in *. inv T.
        }
        rename t into mem_tgt1.
        steps.
        hret _; ss. iModIntro. iSplitL; ss.
        iExists _, _, _. iSplitR; ss. iPureIntro. esplits; et; cbn.
        - ii. unfold Mem.free in *. des_ifs. ss. unfold update. des_ifs.
          replace (memk_src0 b0 ofs0) with (@URA.unit (Excl.t val)); cycle 1.
          { hexploit (SIM b0 ofs0); et. intro T. rewrite Heq0 in *. rewrite Heq in *. inv T; ss. }
          econs.
        - unfold Mem.free in *. des_ifs.
        - rr in WFSRC. rr. ii. unfold Mem.free in *. des_ifs. ss. unfold update in *. des_ifs; et.
        - rr in WFTGT. rr. ii. unfold Mem.free in *. des_ifs. ss. unfold update in *. des_ifs; et.
      }
    }





    econs; ss.
    { unfold loadF. init.
      { harg. fold wf. steps.
        destruct x as [[[b ofs] v]|]; cycle 1.
        { mDesAll; des; clarify.
          (*** TODO: remove redundancy with u (context) case ***)
          (*** COPY START ***)
          des_ifs_safe (mDesAll; ss). des; subst.
          steps. destruct v; ss. clarify. steps.
          renamer.
          rename n into b. rename z into ofs.

          hexploit (SIM b ofs); et. intro T. unfold Mem.load in *. rewrite _UNWRAPU1 in T. inv T.
          steps.
          hret _; ss. iModIntro. iSplitL; ss; et.
          (*** COPY END ***)
        }
        hide_k.
        des_ifs_safe (mDesAll; ss). des; subst. clarify. rewrite Any.upcast_downcast in *. clarify.
        steps. unhide_k. steps. astart 0. astop.
        renamer.
        rename WF into SIMWF.
        mCombine "INV" "A". mOwnWf "INV".
        assert(T: memk_src0 b ofs = (Some v)).
        { clear - WF.
          dup WF.
          eapply Auth.auth_included in WF. des.
          eapply pw_extends in WF. eapply pw_extends in WF. spc WF. rewrite _points_to_hit in WF. des; ss.
          eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
        }
        hexploit SIM; et. intro U. rewrite T in U. inv U; ss. unfold Mem.load.
        mDesOwn "INV".
        force_r; ss. clarify. steps. force_l. esplits. steps.
        hret _; ss. iModIntro. iFrame. iSplitL; et.
      }
      { harg. fold wf. steps.
        des_ifs_safe (mDesAll; ss). des; subst.
        steps. destruct v; ss. clarify. rewrite Any.upcast_downcast in *. clarify. rewrite _UNWRAPU. steps.
        renamer.
        rename n into b. rename z into ofs.

        hexploit (SIM b ofs); et. intro T. unfold Mem.load in *. rewrite _UNWRAPU2 in T. inv T.
        steps.
        hret _; ss. iModIntro. iSplitL; ss; et.
      }
    }





    econs; ss.
    { unfold storeF. init.
      { harg. fold wf. steps. hide_k.
        destruct x as [[[b ofs] v1]|]; cycle 1.
        { mDesAll; des; clarify.
          (*** TODO: remove redundancy with u (context) case ***)
          (*** COPY START ***)
          des_ifs_safe (mDesAll; ss). des; subst.
          unhide_k. steps.
          renamer.
          destruct v; ss. clarify. rename n into b. rename z into ofs.

          force_r.
          { hexploit (SIM b ofs); et. intro T. unfold Mem.store in *. des_ifs. inv T. }
          steps. rename t into mem_tgt1.
          hret _; ss. iModIntro. iSplitL; ss. iExists _, _, _; ss. iSplitR; ss. iPureIntro.
          esplits; ss; et.
          - ii. unfold Mem.store in *. des_ifs. ss. des_ifs. bsimpl; des; des_sumbool; subst.
            hexploit (SIM b0 ofs0); et. intro T. rewrite Heq in *. rewrite Heq0 in *. inv T. econs.
          - unfold Mem.store in *. des_ifs.
          - clear - _UNWRAPU0 WFSRC. ii. unfold Mem.store in *. des_ifs; ss. des_ifs; et.
            + bsimpl; des; des_sumbool; subst. et.
          - clear - _UNWRAPU1 WFTGT. ii. unfold Mem.store in *. des_ifs; ss. des_ifs; et.
            + bsimpl; des; des_sumbool; subst. et.
          (*** COPY END ***)
        }
        des_ifs_safe (mDesAll; ss). des; subst. clarify. rewrite Any.upcast_downcast in *. clarify.
        steps. unhide_k. steps. astart 0. astop.
        renamer.
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
        hexploit SIM; et. intro U. rewrite T in U. inv U; ss. unfold Mem.store. des_ifs. steps.
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
        iExists _, _, _. iSplitR "INV"; et. iPureIntro. esplits; ss; et.
        - ii. cbn. des_ifs.
          + bsimpl; des; des_sumbool; subst. do 2 spc SIM. rewrite Heq in *. rewrite T in *. inv SIM.
            unfold memk_src1. rewrite ! dec_true; ss. econs.
          + replace (memk_src1 b0 ofs0) with (memk_src0 b0 ofs0); et.
            unfold memk_src1. des_ifs; bsimpl; des; des_sumbool; clarify; ss.
        - ii. ss. des_ifs.
          + bsimpl; des; des_sumbool; subst. eapply WFTGT; et.
          + eapply WFTGT; et.
      }
      { harg. fold wf. mDesAll; des; clarify. steps.
        renamer.
        destruct v; ss. clarify. rename n into b. rename z into ofs.

        force_r.
        { hexploit (SIM b ofs); et. intro T. unfold Mem.store in *. des_ifs. inv T. }
        steps. rename t into mem_tgt1.
        hret _; ss. iModIntro. iSplitL; ss. iExists _, _, _; ss. iSplitR; ss. iPureIntro.
        esplits; ss; et.
        - ii. unfold Mem.store in *. des_ifs. ss. des_ifs. bsimpl; des; des_sumbool; subst.
          hexploit (SIM b0 ofs0); et. intro T. rewrite Heq0 in *. rewrite Heq in *. inv T. econs.
        - unfold Mem.store in *. des_ifs.
        - clear - _UNWRAPU0 WFSRC. ii. unfold Mem.store in *. des_ifs; ss. des_ifs; et.
          + bsimpl; des; des_sumbool; subst. et.
        - clear - _UNWRAPU1 WFTGT. ii. unfold Mem.store in *. des_ifs; ss. des_ifs; et.
          + bsimpl; des; des_sumbool; subst. et.
      }
    }





    econs; ss.
    { unfold cmpF. init.
      { harg. fold wf. steps. hide_k.
        destruct x as [[result resource]|]; cycle 1.
        { mDesAll; des; clarify.
          (*** TODO: remove redundancy with u (context) case ***)
          (*** COPY START ***)
          des_ifs_safe (mDesAll; ss). des; subst.
          unhide_k. steps.
          renamer.
          sym in _UNWRAPU.
          assert(T: forall b ofs, Mem.valid_ptr memu_src0 b ofs -> Mem.valid_ptr mem_tgt0 b ofs).
          { clear - SIM. i. unfold Mem.valid_ptr in *.
            hexploit (SIM b ofs); et. intro T. unfold is_some in *. des_ifs. inv T. }
          match goal with
          | |- context[unwrapU ?x] => replace x with (Some b); cycle 1
          end.
          { (*** TODO: make lemma ***)
            unfold vcmp in *. des_ifs; ss; bsimpl; des; des_sumbool; subst; ss; erewrite T in *; ss.
          }
          steps. destruct b.
          - steps. hret _; ss. iModIntro. iSplitL; ss. iExists _, _, _; ss. iSplitR; ss.
          - steps. hret _; ss. iModIntro. iSplitL; ss. iExists _, _, _; ss. iSplitR; ss.
          (*** COPY END ***)
        }
        des_ifs_safe (mDesAll; ss). des; subst. clarify.
        steps. unhide_k. steps. astart 0. astop.
        renamer.
        rename WF into SIMWF.
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
          { erewrite URA.add_comm with (b:=(a2, a3) |-> [a4]) in WF.
            rewrite URA.add_assoc in WF. eapply URA.wf_mon in WF; et. }
          rewrite URA.add_comm in WF. eapply URA.wf_mon in WF. ur in WF; ss. steps.
          replace (dec a a2 && dec a0 a3) with false; cycle 1.
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
      { harg. fold wf. mDesAll; des; clarify. steps.
        renamer.
        sym in _UNWRAPU.
        assert(T: forall b ofs, Mem.valid_ptr memu_src0 b ofs -> Mem.valid_ptr mem_tgt0 b ofs).
        { clear - SIM. i. unfold Mem.valid_ptr in *.
          hexploit (SIM b ofs); et. intro T. unfold is_some in *. des_ifs. inv T. }
        match goal with
        | |- context[unwrapU ?x] => replace x with (Some b); cycle 1
        end.
        { (*** TODO: make lemma ***)
          unfold vcmp in *. des_ifs; ss; bsimpl; des; des_sumbool; subst; ss; erewrite T in *; ss.
        }
        steps. destruct b.
        - steps. hret _; ss. iModIntro. iSplitL; ss. iExists _, _, _; ss. iSplitR; ss.
        - steps. hret _; ss. iModIntro. iSplitL; ss. iExists _, _, _; ss. iSplitR; ss.
      }
    }
  Unshelve.
    all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
