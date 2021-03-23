Require Import Mem0 Mem1 Mem2 HoareDef SimModSem.
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
Require Import HTactics Logic YPM.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



(*** black + delta --> new_black ***)
Definition add_delta_to_black `{M: URA.t} (b: URA.auth_t) (w: URA.auth_t): URA.auth_t :=
  match b, w with
  | URA.excl e _, URA.frag f1 => URA.excl (URA.add e f1) URA.unit
  | _, _ => URA.boom
  end
.


(* Notation "wf n *)
(* '------------------------------------------------------------------' *)
(* src0 tgt0 *)
(* '------------------------------------------------------------------' *)
(* src1 tgt1 *)
(* '------------------------------------------------------------------' *)
(* src2 tgt2" := *)
(*   (sim_itree wf n (([(_, src0)], src1), src2) (([(_, tgt0)], tgt1), tgt2)) *)
(*     (at level 60, *)
(*      format "wf  n '//' *)
(* '------------------------------------------------------------------' '//' *)
(* src0 '//' *)
(* tgt0 '//' *)
(* '------------------------------------------------------------------' '//' *)
(* src1 '//' *)
(* tgt1 '//' *)
(* '------------------------------------------------------------------' '//' *)
(* src2 '//' '//' '//' *)
(* tgt2 '//' *)
(* "). *)
(******** TODO: it works in emacs but fails in coqc -- try coq 8.13 and uncomment it ***********)

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



Tactic Notation "ur" := try rewrite ! URA.unfold_wf; try rewrite ! URA.unfold_add; cbn.
Tactic Notation "ur" "in" hyp(H)  := try rewrite ! URA.unfold_wf in H; try rewrite ! URA.unfold_add in H; cbn in H.

Section AUX.
  Context {K: Type} `{M: URA.t}.
  Let RA := URA.pointwise K M.

  Lemma pw_extends (f0 f1: K -> M) (EXT: @URA.extends RA f0 f1): forall k, <<EXT: URA.extends (f0 k) (f1 k)>>.
  Proof. ii. r in EXT. des. subst. ur. ss. eexists; et. Qed.
  (* Lemma pw_unfold_wf (f: K -> M): (forall k, URA.wf (f k)) -> @URA.wf RA f. Proof. i. ss. Qed. *)

  (* Lemma empty_wf: forall k, URA.wf ((@URA.unit RA) k). *)
  (* Proof. ii; ss. eapply URA.wf_unit. Qed. *)

  (* Lemma update_wf: forall `{Dec K} (f: @URA.car RA) k v (WF: URA.wf f) (WF: URA.wf v), URA.wf (update f k v: (@URA.car RA)). *)
  (* Proof. ii. unfold update. des_ifs; ss. Qed. *)

  Lemma lookup_wf: forall (f: @URA.car RA) k (WF: URA.wf f), URA.wf (f k).
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

End AUX.

Section AUX.
  Context `{Σ: GRA.t}.
  Definition Univ {X: Type} (P: X -> iProp): iProp := fun r => forall x, P x r.
End AUX.
Notation "'Forall' x .. y , p" := (Univ (fun x => .. (Univ (fun y => p)) ..))
                                    (at level 200, x binder, right associativity,
                                     format "'[' 'Forall'  '/  ' x  ..  y ,  '/  ' p ']'").




Definition _points_to (loc: block * Z) (vs: list val): Mem1._memRA :=
  let (b, ofs) := loc in
  (fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length vs))))%Z
                  then URA.of_RA.just (List.nth_error vs (Z.to_nat (_ofs - ofs))) else ε)
.

(* Opaque _points_to. *)
Lemma unfold_points_to loc vs:
  _points_to loc vs =
  let (b, ofs) := loc in
  (fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length vs))))%Z
                  then URA.of_RA.just (List.nth_error vs (Z.to_nat (_ofs - ofs))) else ε)
.
Proof. refl. Qed.

Opaque points_to.
Opaque _points_to.

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

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  (* Eval compute in (@RA.car (RA.excl Mem.t)). *)
  Eval compute in (@URA.car Mem1._memRA).
  Inductive sim_loc: option val -> URA.car (t:=URA.of_RA.t (RA.excl val)) -> Prop :=
  | sim_loc_present v: sim_loc (Some v) (URA.of_RA.just (Some v))
  | sim_loc_absent: sim_loc None ε
  .

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists mr_src (mem_tgt: Mem.t),
        (<<SRC: mrps_src0 = Maps.add "Mem" (mr_src, tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "Mem" (ε, mem_tgt↑) Maps.empty>>) /\
        (* (<<SIM: forall b ofs, sim_loc ((mem_tgt.(Mem.cnts)) b ofs) (mem_src b ofs)>>) *)
        (* (<<SIM: forall b ofs v, (mem_tgt.(Mem.cnts) b ofs = Some v) -> iHyp (⌜True⌝) mem_src>>) *)
        (* (<<SIM: iHyp (Forall b ofs v, ⌜mem_tgt.(Mem.cnts) b ofs = Some v⌝ -* Own (GRA.embed ((b, ofs) |-> [v]))) mem_src>>) *)
        (<<SIM: iHyp (Exists mem_src, Own (GRA.embed ((URA.black mem_src): URA.car (t:=Mem1.memRA))) **
                                          (* (Forall b ofs, ⌜~(b = 0 /\ ofs = 0%Z)⌝ -* *)
                                          (*                  match mem_tgt.(Mem.cnts) b ofs with *)
                                          (*                  | Some v => Own (GRA.embed ((b, ofs) |-> [v])) *)
                                          (*                  | None => ⌜True⌝ *)
                                          (*                  end) *)
                                          (⌜forall b ofs, sim_loc ((mem_tgt.(Mem.cnts)) b ofs) (mem_src b ofs)⌝)
                     ) mr_src>>) /\
        (<<WFTGT: forall b ofs v, mem_tgt.(Mem.cnts) b ofs = Some v -> <<NB: b < mem_tgt.(Mem.nb)>> >>)
  .

  Hint Resolve sim_itree_mon: paco.

  (* Lemma just_wf `{M: RA.t}: forall (x: @RA.car M), RA.wf x -> @URA.wf (URA.of_RA.t M) (URA.of_RA.just x). *)
  (* Proof. i; ss. Qed. *)

  (* Opaque URA.of_RA.t. *)
  (* Opaque URA.auth. *)
  (* Opaque URA.pointwise. *)
  Opaque URA.unit.

  Ltac Ztac := all_once_fast ltac:(fun H => first[apply Z.leb_le in H|apply Z.ltb_lt in H|apply Z.leb_gt in H|apply Z.ltb_ge in H|idtac]).

  Theorem correct: ModSemPair.sim Mem2.MemSem Mem0.MemSem.
  Proof.
   econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. esplits; ss; et. hexploit gwf_dummy; i. iRefresh.
      eexists; iRefresh. iSplitP; ss.
      { eexists. rewrite URA.unit_id. refl. }
      ii. econs.
    }

    econs; ss.
    { unfold allocF. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      iRefresh. iPure PRE. des. clarify. apply Any.upcast_inj in PRE. des; clarify.
      steps. rewrite Any.upcast_downcast in *. steps.
      do 2 iDestruct SIM. iPure A.
      set (blk := (Mem.nb mem_tgt)). rename x into sz. rename x0 into mem_src0.

      unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l. exists 0. steps.

      eapply own_upd in SIM; cycle 1; [|rewrite intro_iHyp in SIM; iMod SIM].
      { eapply GRA.embed_updatable.
        eapply URA.auth_alloc2.
        instantiate (1:=(_points_to (blk, 0%Z) (repeat (Vint 0) sz))).
        (* instantiate (1:=(fun _b _ofs => if (dec _b blk) && ((0 <=? _ofs) && (_ofs <? Z.of_nat sz))%Z then inl (Some (Vint 0)) else inr tt)). *)
        iOwnWf SIM. iRefresh.
        clear - WF WFTGT A.
        ss. do 2 ur. ii. rewrite unfold_points_to. des_ifs.
         - bsimpl. des. des_sumbool. subst. hexploit (A blk k0); et. intro T. inv T; [|eq_closure_tac].
           + exploit WFTGT; et. i; des. lia.
           + rewrite URA.unit_idl. Ztac. rewrite repeat_length in *. rewrite Z.sub_0_r. rewrite repeat_nth_some; [|lia]. ur. ss.
         - rewrite URA.unit_id. do 2 eapply lookup_wf. eapply GRA.embed_wf in WF. des. ur in WF. admit "black wf".
      }
      rewrite <- GRA.embed_add in SIM. rewrite own_sep in SIM. iDestruct SIM.

      force_l. eexists. hret_tac SIM A0.
      - split; [|refl]; iRefresh. eexists; iRefresh. iSplitP; ss.
      - cbn. esplits; et.
        + eexists; iRefresh. iSplitL SIM; et. ii.
          destruct (mem_tgt.(Mem.cnts) blk ofs) eqn:T.
          { exfalso. exploit WFTGT; et. i; des. lia. }
          ss. do 2 ur.
          exploit A; et. rewrite T. intro U. inv U. rewrite unfold_points_to. ss. rewrite repeat_length.
          destruct (dec b blk); subst; ss.
          * unfold update. des_ifs_safe. rewrite <- H0. rewrite URA.unit_idl. des_ifs.
            { rewrite Z.sub_0_r. bsimpl. des. Ztac. rewrite repeat_nth_some; try lia. econs. }
            { econs. }
          * rewrite URA.unit_id. unfold update. des_ifs.
        + clear - WFTGT. i. ss. unfold update in *. des_ifs. exploit WFTGT; et.
    }
    econs; ss.
    { unfold freeF. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      iRefresh. do 3 iDestruct PRE. iPure PRE. iPure A. clarify. apply Any.upcast_inj in PRE. des; clarify.
      do 2 iDestruct SIM. iPure A.
      steps. rewrite Any.upcast_downcast in *. steps.

      unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l. exists 0. steps.

      rename n into b. rename z into ofs. rename x0 into mem_src0. rename x into v.
      iMerge SIM A0. rewrite <- own_sep in SIM. rewrite GRA.embed_add in SIM.
      iOwnWf SIM. eapply GRA.embed_wf in WF; des.
      assert(HIT: mem_src0 b ofs = URA.of_RA.just (Some v)).
      { clear - WF.
        Local Transparent points_to.
        eapply URA.auth_included in WF. des. eapply pw_extends with (k:=b) in WF. eapply pw_extends with (k:=ofs) in WF.
        ss. des_ifs; cycle 1.
        { bsimpl. des; des_sumbool; Ztac; try lia. }
        { bsimpl. des. Ztac. rewrite Z.sub_diag in *. ss. admit "ez -- of_RA extends && RA.excl extends". }
      }
      set (mem_src1 := fun _b _ofs => if dec _b b && dec _ofs ofs then URA.of_RA.unit else mem_src0 _b _ofs).
      assert(WF': URA.wf (mem_src1: URA.car (t:=Mem1._memRA))).
      { clear - WF. unfold mem_src1. do 2 ur. ii. eapply URA.wf_mon in WF. ur in WF. des.
        des_ifs; et.
        - rp; [eapply URA.wf_unit|ss].
        - do 2 eapply lookup_wf; et.
      }
      hexploit (A b ofs); et. rewrite HIT. intro B. inv B.
      force_r.
      { unfold Mem.free in *. des_ifs. }
      rename mem_tgt into mem_tgt0. rename t into mem_tgt1.

      eapply own_upd in SIM; cycle 1; [|rewrite intro_iHyp in SIM; iMod SIM].
      { eapply GRA.embed_updatable.
        Local Transparent points_to.
        eapply URA.auth_dealloc.
        instantiate (1:=mem_src1).
        clear - WF'. rewrite <- (unfold_points_to (b, ofs) [v]).

        r. i. rewrite URA.unit_idl.
        Local Opaque Mem1._memRA.
        ss. destruct H; clear H. (*** coq bug; des infloops ***) des. clarify.
        esplits; et.
        Local Transparent Mem1._memRA.
        unfold mem_src1. ss.
        apply func_ext. intro _b. apply func_ext. intro _ofs.
        des_ifs.
        - bsimpl; des; des_sumbool; subst.
          subst mem_src1. do 2 ur in WF'. do 2 spc WF'. des_ifs; bsimpl; des; des_sumbool; ss.
          clear - H0.
          do 2 ur in H0.
          specialize (H0 b ofs).
          des_ifs; bsimpl; des; des_sumbool; Ztac; try lia. try rewrite Z.sub_diag in *; ss.
          admit "ez".
        - rewrite unfold_points_to in *. do 2 ur. do 2 ur in H0.
          bsimpl. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia; try rewrite URA.unit_idl; try refl.
      }
      steps. iRefresh. force_l. eexists. hret_tac SIM (@URA.unit Σ).
      { split; [|refl]. ss. }
      { ss. esplits; ss; et.
        - eexists mem_src1; iRefresh. iSplitP; ss. ii.
          { unfold Mem.free in _UNWRAPU. des_ifs. ss.
            subst mem_src1. ss.
            destruct (classic (b = b0 /\ ofs = ofs0)); des; clarify.
            - unfold update. des_ifs. econs.
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
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      iRefresh. do 2 iDestruct PRE. iPure PRE. iPure A. clarify. apply Any.upcast_inj in PRE. des; clarify.
      do 2 iDestruct SIM. iPure A.
      steps. rewrite Any.upcast_downcast in *. steps.

      unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l. exists 0. steps.
      rename n into b. rename z into ofs. rename x into mem_src0.
      iMerge SIM A0. rewrite <- own_sep in SIM. rewrite GRA.embed_add in SIM. iOwnWf SIM.
      assert(T: mem_src0 b ofs = inl (Some v)).
      { clear - WF.
        apply GRA.embed_wf in WF. des; ss.
        Local Transparent points_to URA.add URA.wf.
        ss. des. do 2 spc WF0. rr in WF. des. ss.
        des_ifs; bsimpl; des; des_sumbool; ss;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
            try rewrite Z.sub_diag in *; try lia; ss.
        Local Opaque points_to URA.add URA.wf.
      }
      exploit A; et. intro U. rewrite T in U. inv U; ss. unfold Mem.load.
      rewrite <- GRA.embed_add in SIM. rewrite own_sep in SIM. iDestruct SIM.
      force_r; ss. clarify. steps. force_l. esplits.
      hret_tac SIM A0.
      { split; [|refl]; iRefresh. iSplitP; ss. }
      { ss. esplits; eauto. eexists; iRefresh. iSplitP; ss; et. }
    }
    econs; ss.
    { unfold storeF. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      iRefresh. do 3 iDestruct PRE. iPure PRE. iPure A. clarify. apply Any.upcast_inj in PRE. des; clarify.
      do 2 iDestruct SIM. iPure A.
      steps. rewrite Any.upcast_downcast in *. steps.

      unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l. exists 0. steps.
      rename n into b. rename z into ofs. rename x into mem_src0.
      iMerge SIM A0. rewrite <- own_sep in SIM. rewrite GRA.embed_add in SIM. iOwnWf SIM.
      assert(T: mem_src0 b ofs = inl (Some v)).
      { clear - WF.
        apply GRA.embed_wf in WF. des; ss.
        Local Transparent points_to URA.add URA.wf.
        ss. des. do 2 spc WF0. rr in WF. des. ss.
        des_ifs; bsimpl; des; des_sumbool; ss;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
            try rewrite Z.sub_diag in *; try lia; ss.
        Local Opaque points_to URA.add URA.wf.
      }
      exploit A; et. intro U. rewrite T in U. inv U; ss. unfold Mem.load.
      rewrite <- GRA.embed_add in SIM. rewrite own_sep in SIM. iDestruct SIM.
      force_r; ss. clarify. steps. force_l. esplits.
      hret_tac SIM A0.
      { split; [|refl]; iRefresh. iSplitP; ss. }
      { ss. esplits; eauto. eexists; iRefresh. iSplitP; ss; et. }
    }
    { unfold loadF. init. harg_tac. des; clarify.
      unfold interp_hCallE_tgt, APC. steps. anytac. ss.
      steps. force_l. exists 0. steps. anytac. ss. steps.
      rewrite URA.unit_idl in *. rewrite GRA.embed_add in *. apply_all_once GRA.embed_wf. des.
      rename n into b. rename z into ofs.
      assert(T: mem_src b ofs = inl (Some v)).
      { Local Transparent points_to URA.add URA.wf URA.unit.
        clear - VALID.
        ss. des. do 2 spc VALID0. rr in VALID. des. ss.
        des_ifs; bsimpl; des; des_sumbool; ss;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
            try rewrite Z.sub_diag in *; try lia; ss.
        Local Opaque points_to URA.add URA.wf URA.unit.
      }
      exploit SIM; et. intro U. rewrite T in U. inv U; ss. unfold Mem.load.
      force_r; ss. clarify. steps. force_l. esplits.
      hret_tac (GRA.embed (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) (GRA.embed ((b, ofs) |-> [v0])); ss.
      esplits; eauto.
    }


    steps. iRefresh. force_l. eexists. hret_tac




      assert(SIM': forall b ofs, sim_loc (Mem.cnts mem_tgt' b ofs) (mem_src' b ofs)).
      { i.
        unfold Mem.free in _UNWRAPU. des_ifs. ss.
        subst mem_src'. ss.
        destruct (classic (b = b0 /\ ofs = ofs0)); des; clarify.
        - destruct H0; clarify. (**** TODO: FIX ****) unfold update. des_ifs. econs.
        - des_ifs.
          { Psimpl. bsimpl; des; des_sumbool; ss; clarify. destruct H0; ss. destruct H1; ss. (**** TODO: FIX ****)}
          replace (update (Mem.cnts mem_tgt) b (update (Mem.cnts mem_tgt b) ofs None) b0 ofs0) with
              (Mem.cnts mem_tgt b0 ofs0); cycle 1.
          { unfold update. des_ifs. Psimpl. des_ifs; bsimpl; des; des_sumbool; ss; clarify. }
          et.
      }

      iMerge SIM A0. rewrite <- own_sep in SIM. rewrite GRA.embed_add in SIM.
      eapply own_upd in SIM; cycle 1; [|rewrite intro_iHyp in SIM; iMod SIM].
      { eapply GRA.embed_updatable.
        Local Transparent points_to.
        eapply URA.auth_dealloc.
        Local Opaque points_to.


        instantiate (1:=(_points_to (blk, 0%Z) (repeat (Vint 0) sz))).
        (* instantiate (1:=(fun _b _ofs => if (dec _b blk) && ((0 <=? _ofs) && (_ofs <? Z.of_nat sz))%Z then inl (Some (Vint 0)) else inr tt)). *)
        iOwnWf SIM. iRefresh.
        clear - WF WFTGT A.
        ss. ii. des_ifs.
         - bsimpl. des. des_sumbool. subst. hexploit (A blk k0); et. intro T. inv T; [|eq_closure_tac].
           exploit WFTGT; et. i; des. lia.
         - specialize (A k k0). inv A; eq_closure_tac.
         - rewrite Z.sub_0_r. bsimpl. des. des_sumbool. subst. apply_all_once Z.leb_le. apply_all_once Z.ltb_lt.
           intro B. apply nth_error_None in B. lia.
      }
      rewrite <- GRA.embed_add in SIM. rewrite own_sep in SIM. iDestruct SIM.

      force_l. eexists. hret_tac SIM A0.
      - split; [|refl]; iRefresh. eexists; iRefresh. iSplitP; ss.
      - cbn. esplits; et.
        + eexists; iRefresh. iSplitL SIM; et. ii.
          destruct (mem_tgt.(Mem.cnts) blk ofs) eqn:T.
          { exfalso. exploit WFTGT; et. i; des. lia. }
          exploit A; et. rewrite T. intro U. inv U. ss. rewrite repeat_length.
          destruct (dec b blk).
          * subst. ss. unfold update. des_ifs_safe. des_ifs.
            { rewrite Z.sub_0_r. bsimpl. des. apply_all_once Z.leb_le. apply_all_once Z.ltb_lt.
              rewrite repeat_nth_some; try lia. econs. }
            { econs. }
          * ss. unfold update. des_ifs_safe.
            hexploit (A b ofs); et. intro V. inv V; ss.
            { econs. }
            { econs. }
        + clear - WFTGT. i. ss. unfold update in *. des_ifs. exploit WFTGT; et.
    }
            des_ifs.
            { eq_closure_tac. }
          * ss.
            destruct (mem_src0 blk ofs) eqn:U.
            {
            assert(mem_tgt.(Mem.cnts) blk ofs = None).
            {
        +
             exploit A; et. bsimpl. des. des_sumbool. subst. hexploit (A blk k0); et. intro T. inv T; [|eq_closure_tac].
           exploit WFTGT; et. i; des. lia.
         -
           clear - H1. subst blk. ss.
           apply_all_once Z.leb_le. apply_all_once Z.ltb_lt.
           bsimpl; des; des_sumbool; ss.
        instantiate(1:=(fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length (List.repeat 0 sz)))))%Z
                              then inl (List.nth_error (List.repeat 0 sz) (Z.to_nat (_ofs - ofs))) else inr tt)).
        instantiate (1:=((blk, 0%Z) |-> (List.repeat (Vint 0) sz))).
        instantiate (1:= echo_black x (z :: ns) ⋅ echo_white x (z :: ns)).
        eapply URA.auth_update. rr. ii. des; ss. destruct ctx; ss; clarify.
      }
      iUpdate SIM.
      unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l. exists 0. steps.

      force_l. eexists.
      hret_tac (@URA.unit Σ) (@URA.unit Σ).
      { split; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. }

      { split; eauto. iRefresh. iSplitL PRE; eauto. rr. f_equal.
        rewrite <- Z.negb_odd. rewrite negb_if. des_ifs. }
      { unfold wf. esplits; eauto. }
      rewrite unfold_APC. steps.


      assert (x = Z.odd n); subst.
      { hexploit bw_ra_merge; et. intro T. iSpecialize T SIM. iSpecialize T PRE. iPure T. auto. }
      unfold body_to_tgt. unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l. exists 0. steps. rewrite unfold_APC. steps.
      rewrite Any.upcast_downcast. force_l. eexists.
      hret_tac SIM PRE.
      { split; eauto. iRefresh. iSplitL PRE; eauto. rr. f_equal.
        rewrite <- Z.negb_odd. rewrite negb_if. des_ifs. }
      { unfold wf. esplits; eauto. }
    }




    { unfold allocF. init. harg_tac. des; clarify.
      unfold interp_hCallE_tgt, APC. steps. anytac. ss.
      steps. force_l. exists 0. steps. force_l. exists (Vptr (Mem.nb mem_tgt) 0).
      set (blk := (Mem.nb mem_tgt)). rename x into sz.
      assert(WFA: forall ofs, mem_src (Mem.nb mem_tgt) ofs = inr tt).
      { i.
        destruct (mem_src (Mem.nb mem_tgt) ofs) eqn:A; cycle 1.
        { des_u; ss. }
        destruct o.
        - admit "ez - add tgt wf".
        - admit "ez - inl None is boom in RA.excl".
      }
      hret_tac (GRA.embed (add_delta_to_black
                               (URA.black (mem_src: URA.car (t:=Mem1._memRA)))
                               (points_to (blk, 0%Z) (repeat (Vint 0) sz)): URA.car (t:=Mem1.memRA)))
      (GRA.embed ((blk, 0%Z) |-> (List.repeat (Vint 0) sz))).
      { Local Opaque URA.add. etrans.
        { eapply URA.extends_updatable. eexists; et. }
        erewrite GRA.embed_add. eapply GRA.embed_updatable.
        ss. des_ifs. eapply URA.auth_alloc2.
        eapply URA.wf_mon in VALID.
        eapply GRA.embed_wf in VALID. des.
        clear - VALID WFA Heq SIM.
        Local Transparent URA.add points_to.
        ss. des. unfold URA.white in Heq. clarify.
        ii. des_ifs; ss.
        - bsimpl; des; des_sumbool; clarify.
          exploit WFA; et. intro A. rewrite A in *; ss.
        - specialize (VALID0 k k0). bsimpl; des; des_sumbool; clarify; des_ifs.
        - specialize (VALID0 k k0). bsimpl; des; des_sumbool; clarify; des_ifs.
          apply_all_once Z.leb_le. apply_all_once Z.ltb_lt.
          intro A. apply nth_error_None in A. rewrite repeat_length in *.
          apply inj_le in A. rewrite Z2Nat.id in A; cycle 1.
          { lia. }
          lia.
          Local Opaque URA.add points_to.
      }
      { esplits; ss. }
      { Local Opaque URA.wf.
        Local Opaque URA.add points_to.
        Local Transparent points_to.
        ss. esplits; ss. i. ss.
        destruct (dec b blk).
        + subst. unfold blk. unfold update. des_ifs_safe. ss.
          des_ifs.
          * bsimpl; des; try rewrite Z.leb_le in *; try rewrite Z.ltb_lt in *.
            Local Transparent URA.add.
            s.
            Local Opaque URA.add.
            des_ifs; bsimpl; des; des_sumbool; ss; clarify; try rewrite Z.leb_le in *; try rewrite Z.ltb_lt in *;
              try rewrite Z.leb_gt in *; try rewrite Z.ltb_ge in *; try lia; et.
            { exploit WFA; et. intro A. rewrite A in *; ss. }
            { exploit WFA; et. intro A. rewrite A in *; ss. }
            { rewrite Z.sub_0_r.
              destruct (nth_error (repeat (Vint 0) sz) (Z.to_nat ofs)) eqn:U.
              - eapply nth_error_In in U. eapply repeat_spec in U. subst. econs; et.
              - eapply nth_error_None in U. lia.
            }
            { rewrite repeat_length in *. lia. }
          * Local Transparent URA.add.
            s.
            Local Opaque URA.add.
            des_ifs; bsimpl; des; des_sumbool; ss; clarify; try rewrite Z.leb_le in *; try rewrite Z.ltb_lt in *;
              try rewrite Z.leb_gt in *; try rewrite Z.ltb_ge in *; try lia; et;
                try (by exploit WFA; et; intro A; rewrite A in *; ss).
            { rewrite Z.sub_0_r. rewrite repeat_length in *. lia. }
            { econs; eauto. }
            { econs; eauto. }
        + Local Transparent URA.add.
          ss.
          hexploit (SIM b ofs); et. intro A. inv A.
          {
            des_ifs; bsimpl; des; des_sumbool; clarify.
            - unfold update. des_ifs. rewrite <- H1. econs.
            - unfold update. des_ifs. rewrite <- H1. econs.
            - unfold update. des_ifs. rewrite <- H1. econs.
          }
          {
            des_ifs; bsimpl; des; des_sumbool; clarify.
            - unfold update. des_ifs. rewrite <- H1. econs.
            - unfold update. des_ifs. rewrite <- H1. econs.
            - unfold update. des_ifs. rewrite <- H1. econs.
          }
      }
    }
    econs; ss.
    { unfold freeF. init. harg_tac. des; clarify.
      unfold interp_hCallE_tgt, APC. steps. anytac. ss.
      steps. force_l. exists 0. steps. anytac. ss. steps.
      rewrite URA.unit_idl in *. rewrite GRA.embed_add in *. eapply GRA.embed_wf in VALID. des.
      rename n into b. rename z into ofs.
      assert(A: mem_src b ofs = inl (Some v)).
      { Local Transparent URA.wf.
        ss.
        Local Transparent URA.add.
        ss. des_ifs. des. specialize (VALID0 b ofs).
        Local Transparent URA.add.
        clear SIM.
        Local Transparent URA.unit.
        ss. clarify. rr in VALID. des. clarify. ss.
        des_ifs;
          bsimpl; des; des_sumbool; ss;
          repeat des_u;
          clear_tac;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
          try rewrite Z.sub_diag in *;
          try lia; ss.
        Local Opaque URA.wf URA.add URA.unit.
      }

      set (mem_src' := fun _b _ofs => if dec _b b && dec _ofs ofs then inr () else mem_src _b _ofs).
      assert(WF': URA.wf (mem_src': URA.car (t:=Mem1._memRA))).
      { Local Transparent URA.add URA.wf.
        ss. ii. des_ifs.
        ss. clarify.
        subst mem_src'. ss. des_ifs. des. specialize (VALID0 k k0). bsimpl. des; des_sumbool; des_ifs.
        Local Opaque URA.wf URA.add.
      }
      hexploit (SIM b ofs); et. intro B. rewrite A in *. inv B.
      force_r.
      { exfalso. unfold Mem.free in *. des_ifs. }
      rename t into mem_tgt'.
      assert(SIM': forall b ofs, sim_loc (Mem.cnts mem_tgt' b ofs) (mem_src' b ofs)).
      { i.
        unfold Mem.free in _UNWRAPU. des_ifs. ss.
        subst mem_src'. ss.
        destruct (classic (b = b0 /\ ofs = ofs0)); des; clarify.
        - destruct H0; clarify. (**** TODO: FIX ****) unfold update. des_ifs. econs.
        - des_ifs.
          { Psimpl. bsimpl; des; des_sumbool; ss; clarify. destruct H0; ss. destruct H1; ss. (**** TODO: FIX ****)}
          replace (update (Mem.cnts mem_tgt) b (update (Mem.cnts mem_tgt b) ofs None) b0 ofs0) with
              (Mem.cnts mem_tgt b0 ofs0); cycle 1.
          { unfold update. des_ifs. Psimpl. des_ifs; bsimpl; des; des_sumbool; ss; clarify. }
          et.
      }
      force_l. esplits. steps.
      hret_tac (GRA.embed (URA.black (mem_src': URA.car (t:=Mem1._memRA)))) (@URA.unit Σ).
      { rewrite URA.unit_id.
        rewrite ! GRA.embed_add. apply GRA.embed_updatable.
        apply URA.auth_dealloc.
        clear - WF' VALID.
        r. i. rewrite URA.unit_idl.
        ss. destruct H; clear H. (*** coq bug; des infloops ***) des. clarify.
        esplits; et.
        apply func_ext. intro _b. apply func_ext. intro _ofs.
        destruct (classic (b = _b /\ ofs = _ofs)).
        - destruct H; clear H. clarify.
          subst mem_src'. ss. des_ifs; bsimpl; des; des_sumbool; clarify.
          clear - H0.
          Local Transparent URA.wf.
          Local Transparent URA.add.
          specialize (H0 _b _ofs). ss.
          des_ifs; bsimpl; des; des_sumbool;
            try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
              try rewrite Z.sub_diag in *;
              try lia; ss.
          des_u. ss.
        - Psimpl.
          subst mem_src'. s.
          des_ifs; bsimpl; des; des_sumbool;
            try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
              try rewrite Z.sub_diag in *;
              try lia; ss.
          Local Opaque URA.wf.
          Local Opaque URA.add.
      }
      { split; ss. }
      { unfold wf. esplits; eauto. }
    }
    econs; ss.
    { unfold loadF. init. harg_tac. des; clarify.
      unfold interp_hCallE_tgt, APC. steps. anytac. ss.
      steps. force_l. exists 0. steps. anytac. ss. steps.
      rewrite URA.unit_idl in *. rewrite GRA.embed_add in *. apply_all_once GRA.embed_wf. des.
      rename n into b. rename z into ofs.
      assert(T: mem_src b ofs = inl (Some v)).
      { Local Transparent points_to URA.add URA.wf URA.unit.
        clear - VALID.
        ss. des. do 2 spc VALID0. rr in VALID. des. ss.
        des_ifs; bsimpl; des; des_sumbool; ss;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
            try rewrite Z.sub_diag in *; try lia; ss.
        Local Opaque points_to URA.add URA.wf URA.unit.
      }
      exploit SIM; et. intro U. rewrite T in U. inv U; ss. unfold Mem.load.
      force_r; ss. clarify. steps. force_l. esplits.
      hret_tac (GRA.embed (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) (GRA.embed ((b, ofs) |-> [v0])); ss.
      esplits; eauto.
    }
    econs; ss.
    { unfold storeF. init. harg_tac. des; clarify.
      unfold interp_hCallE_tgt, APC. steps. anytac. ss.
      steps. force_l. exists 0. steps. anytac. ss. steps.
      rewrite URA.unit_idl in *. rewrite GRA.embed_add in *. apply_all_once GRA.embed_wf. des.
      rename n into b. rename z into ofs.
      set (mem_src' := fun _b _ofs => if dec _b b && dec _ofs ofs then inl (Some v) else mem_src _b _ofs).
      assert(WF0: URA.wf (mem_src': URA.car (t:=Mem1._memRA))).
      { Local Transparent URA.wf.
        clear - VALID. apply URA.wf_mon in VALID. ss. des.
        ii. specialize (VALID0 k k0). des_ifs_safe. unfold mem_src' in *. des_ifs.
        Local Opaque URA.wf.
      }
      assert(U: mem_src b ofs = inl (Some v_old)).
      { Local Transparent URA.add GRA.to_URA points_to URA.wf URA.unit.
        clear - VALID. ss. des. specialize (VALID0 b ofs). r in VALID. des; clarify. ss.
        des_ifs; bsimpl; des; des_sumbool; ss; subst;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
            try rewrite Z.sub_diag in *; try lia; ss.
        Local Opaque URA.add GRA.to_URA points_to URA.wf URA.unit.
      }
      hexploit SIM; et. intro V. rewrite U in V. inv V; ss. unfold Mem.store. rewrite <- H1. steps.
      force_l. esplit.
      hret_tac (GRA.embed (URA.black (mem_src': URA.car (t:=Mem1._memRA)))) (GRA.embed ((b, ofs) |-> [v])).
      { rewrite ! GRA.embed_add. eapply GRA.embed_updatable.
        clear - VALID WF0. clear VALID.
        Local Transparent URA.add GRA.to_URA points_to URA.wf URA.unit.
        eapply URA.auth_update; et.
        rr. ii. destruct H; clear H. (*** FIXME: des runs infloop ***)
        des. subst. esplits; et.
        subst mem_src'. do 2 (apply func_ext; i). specialize (H0 x x0). specialize (WF0 x x0). ss.
        des_ifs; bsimpl; des; des_sumbool; ss; subst;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
            try rewrite Z.sub_diag in *; try lia; ss.
        Local Opaque URA.add GRA.to_URA points_to URA.wf URA.unit.
      }
      { splits; eauto. }
      { unfold wf. esplits; eauto. esplits; ss; et. des_ifs.
        - bsimpl; des; des_sumbool; ss; subst. unfold mem_src'. des_ifs; bsimpl; des; des_sumbool; ss. econs; et.
        - unfold mem_src'. des_ifs. bsimpl; des; des_sumbool; subst; ss.
      }
    }
    econs; ss.
    { unfold cmpF. init. harg_tac. unfold interp_hCallE_tgt, APC. steps.
      destruct PRE as [[? []] ?]. subst.
      set (resource := c).
      assert (VALIDPTR: forall b ofs v (WF: URA.wf ((URA.black (mem_src: URA.car (t:=Mem1._memRA))) ⋅ ((b, ofs) |-> [v]))),
                 Mem.valid_ptr mem_tgt b ofs = true).
      { clear - SIM. i. cut (mem_src b ofs = inl (Some v)).
        - i. unfold Mem.valid_ptr.
          specialize (SIM b ofs). rewrite H in *. inv SIM. ss.
        - Local Transparent points_to URA.add URA.wf URA.unit.
          ss. des. specialize (WF0 b ofs). r in WF. des; clarify. ss.
          des_ifs; bsimpl; des; des_sumbool; ss; subst;
            try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
              try rewrite Z.sub_diag in *; try lia; ss.
          Local Opaque URA.add GRA.to_URA points_to URA.wf URA.unit.
      }
      force_l. exists 0. steps. force_l. exists (if b then Vint 1 else Vint 0). des; clarify.
      - anytac. ss. steps.
        rewrite URA.unit_idl in *. rewrite GRA.embed_add in *. apply_all_once GRA.embed_wf. des.
        erewrite VALIDPTR; cycle 1.
        { instantiate (1:=v). eapply VALID. }
        steps. hret_tac (GRA.embed (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) resource; ss.
        esplits; eauto.
      - anytac. ss. steps.
        rewrite URA.unit_idl in *. rewrite GRA.embed_add in *. apply_all_once GRA.embed_wf. des.
        erewrite VALIDPTR; cycle 1.
        { instantiate (1:=v). eapply VALID. }
        steps. hret_tac (GRA.embed (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) resource; ss.
        esplits; eauto.
      - anytac. ss. steps.
        rewrite URA.unit_idl in *. repeat rewrite GRA.embed_add in *. apply_all_once GRA.embed_wf. des.
        erewrite VALIDPTR; cycle 1.
        { instantiate (1:=v0). clear - VALID.
          eapply URA.wf_mon. erewrite <- URA.add_assoc. eapply VALID. }
        erewrite VALIDPTR; cycle 1.
        { instantiate (1:=v1). clear - VALID.
          eapply URA.wf_mon. erewrite <- URA.add_assoc.
          erewrite URA.add_comm with (a:=(b1, ofs1) |-> [v1]). eapply VALID. }
        ss. destruct (dec b0 b1); cycle 1.
        { ss. steps. hret_tac (GRA.embed (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) resource; ss.
          esplits; eauto. }
        destruct (dec ofs0 ofs1); cycle 1.
        { ss. steps. hret_tac (GRA.embed (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) resource; ss.
          esplits; eauto. }
        subst. exfalso.
        erewrite URA.add_comm in VALID. eapply URA.wf_mon in VALID.
        Local Transparent points_to URA.add URA.wf URA.unit.
        ss. specialize (VALID b1 ofs1).
        destruct (dec b1 b1); ss. erewrite Z.leb_refl in *. ss.
        replace (ofs1 <? ofs1 + 1)%Z with true in *; ss.
        clear. symmetry. eapply Z.ltb_lt. lia.
        Local Opaque URA.add GRA.to_URA points_to URA.wf URA.unit.
      - anytac. ss. steps.
        rewrite URA.unit_idl in *. rewrite GRA.embed_add in *. apply_all_once GRA.embed_wf. des.
        erewrite VALIDPTR; cycle 1.
        { instantiate (1:=v). eapply VALID. }
        ss. destruct (dec b0 b0); ss. destruct (dec ofs ofs); ss. steps.
        hret_tac (GRA.embed (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) resource; ss.
        esplits; eauto.
      - anytac. ss. steps. rewrite URA.unit_idl in *.
        hret_tac (GRA.embed (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) resource; ss.
        esplits; eauto.
    }
  Qed.

End SIMMODSEM.
