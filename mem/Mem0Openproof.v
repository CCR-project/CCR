Require Import Mem0 Mem1 MemOpen HoareDef SimModSem.
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

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).
  (* Eval compute in (@RA.car (RA.excl Mem.t)). *)
  Eval compute in (@URA.car Mem1._memRA).

  Inductive mem_extends (m0 m1: Mem.t): Prop :=
  | mem_extends_intro
      (NB: m0.(Mem.nb) <= m1.(Mem.nb))
      (CNTS: forall b ofs, (m0.(Mem.cnts) b ofs) = None \/ (m0.(Mem.cnts) b ofs) = (m1.(Mem.cnts) b ofs))
  .

  Global Program Instance mem_extends_PreOrder: PreOrder mem_extends.
  Next Obligation.
    ii. econs; et.
  Qed.
  Next Obligation.
    ii. inv H0; inv H1. econs; et; try lia. ii. repeat spc CNTS. des; et. repeat spc CNTS0. des; eauto with congruence.
  Qed.

  Search (option _ -> option _ -> option _).
  SearchPattern (option _ -> option _ -> option _).

  Definition o_combine X (f: X -> X -> option X) (x0 x1: option X): option X :=
    match x0, x1 with
    | Some x0, Some x1 => do x <- (f x0 x1); Some x
    | Some x0, _ => Some x0
    | _, Some x1 => Some x1
    | _, _ => None
    end
  .

  Definition o_xor X (x0 x1: option X): option X :=
    Eval red in (o_combine (fun _ _ => None) x0 x1)
  .

  (*** memk_src -> memu_src -> mem_tgt ***)
  Inductive sim_loc: URA.car (t:=(Excl.t _)) -> option val -> option val -> Prop :=
  | sim_loc_k v: sim_loc (Some v) None (Some v)
  | sim_loc_u v: sim_loc ε (Some v) (Some v)
  | sim_loc_absent: sim_loc ε None None
  .

  (* Let wf: W -> Prop := *)
  (*   fun '((mr_src, memu_src), (mr_tgt, mem_tgt)) => *)
  (*     exists memk_src, *)
  (*     (<<SRC: iHyp (Own (GRA.embed ((Auth.black memk_src): URA.car (t:=Mem1.memRA)))) mr_src>>) /\ *)
  (*     (<<TGT: mr_tgt = ε>>) /\ *)
  (*     (<<SIM: forall b ofs, sim_loc (memk_src b ofs) (memu_src.(Mem.cnts) b ofs) *)
  (*                                   (mem_tgt.(Mem.cnts) b ofs)>>) *)
  (* . *)

  Definition mem_wf (m0: Mem.t): Prop :=
    forall b ofs v, m0.(Mem.cnts) b ofs = Some v -> <<NB: b < m0.(Mem.nb)>>
  .

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr_src: Σ) (memu_src: Mem.t) (mr_tgt: Σ) (mem_tgt: Mem.t) memk_src,
        (<<SRC: mrps_src0 = (mr_src, memk_src↑)>>) /\
        (<<TGT: mrps_tgt0 = (ε, mem_tgt↑)>>) /\
        (<<SRCR: iHyp (Own (GRA.embed ((Auth.black memk_src): URA.car (t:=Mem1.memRA)))) mr_src>>) /\
        (<<SIM: forall b ofs, sim_loc (memk_src b ofs) (memu_src.(Mem.cnts) b ofs)
                                      (mem_tgt.(Mem.cnts) b ofs)>>) /\
        (<<SIMM: mem_extends memu_src mem_tgt>>) /\
        (<<WFSRC: mem_wf memu_src>>) /\
        (<<WFTGT: mem_wf mem_tgt>>) (*** TODO: put it inside Mem.t? ***)
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
    SIMM holds. (should make lemma)
  + unknown
    By SIMM, we know that memu_src.(nb) <= the new block.
    Therefore, we can allocate new block in memu_src and still satisfy SIM.
    SIMM holds. (should make lemma)
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

It seems like we don't need mem_extends; such information is already present in sim_loc
   ***)

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists mr_src (mem_src: Mem.t) (mem_tgt: Mem.t),
        (<<SRC: mrps_src0 = (mr_src, mem_src↑)>>) /\
        (<<TGT: mrps_tgt0 = (ε, mem_tgt↑)>>) /\
        (<<SIM: iHyp (Exists mem_src, Own (GRA.embed ((Auth.black mem_src): URA.car (t:=Mem1.memRA))) **
                                          (⌜forall b ofs, sim_loc ((mem_tgt.(Mem.cnts)) b ofs) (mem_src b ofs)⌝)) mr_src>>) /\
        (<<WFTGT: forall b ofs v, mem_tgt.(Mem.cnts) b ofs = Some v -> <<NB: b < mem_tgt.(Mem.nb)>> >>) /\
        (<<SIMM: mem_extends mem_src mem_tgt>>)
  .

  Hint Resolve sim_itree_mon: paco.

  (* Lemma just_wf `{M: RA.t}: forall (x: @RA.car M), RA.wf x -> @URA.wf (of_RA.t M) (URA.of_RA.just x). *)
  (* Proof. i; ss. Qed. *)

  (* Opaque of_RA.t. *)
  (* Opaque URA.auth. *)
  (* Opaque URA.pointwise. *)
  Opaque URA.unit.

  (* Lemma or_split: (forall (ab: Σ) (Pa Pb: iProp), iHyp (Pa ∨ Pb) (ab) -> iHyp Pa ab \/ iHyp Pb ab). *)
  (*   { clear - Σ. ii. unfold iHyp in *. r in H. et. } *)
  (* Qed. *)
Ltac iDestruct H :=
  match type of H with
  | iHyp (Exists _, _) _ => destruct H as [? H]; iRefresh
  | iHyp (_ ** _) _ =>
    let name0 := fresh "A" in
    apply sepconj_split in H as [? [? [H [name0 ?]]]]; subst; iRefresh
  | iHyp (_ ∧ ⌜ _ ⌝) _ =>
    let name0 := fresh "B" in
    destruct H as [H name0]; iRefresh; iPure name0
  | iHyp (⌜ _ ⌝ ∧ _) _ =>
    let name0 := fresh "B" in
    destruct H as [name0 H]; iRefresh; iPure name0
  | iHyp (_ ∨ _) _ =>
    destruct H as [H|H]; iRefresh
  (*** TODO: make iDestructL/iDestructR ***)
  end.

  (* Definition __NEVER_USE_THIS___KSRC__ := "__KSRC__". *)
  (* Definition __NEVER_USE_THIS___KTGT__ := "__KTGT__". *)

  Definition __hide_mark__ A (a : A) : A := a.
  Lemma intro_hide_mark: forall A (a: A), a = __hide_mark__ a. refl. Qed.

  Ltac hide_k := 
    match goal with
    | [ |- (gpaco6 _ _ _ _ _ _ _ _ (_, ?isrc >>= ?ksrc) (_, ?itgt >>= ?ktgt)) ] =>
      rewrite intro_hide_mark with (a:=ksrc);
      rewrite intro_hide_mark with (a:=ktgt);
      let name0 := fresh "__KSRC__" in set (__hide_mark__ ksrc) as name0; move name0 at top;
      let name0 := fresh "__KTGT__" in set (__hide_mark__ ktgt) as name0; move name0 at top
    end.

  Ltac unhide_k :=
    do 2 match goal with
    | [ H := __hide_mark__ _ |- _ ] => subst H
    end;
    rewrite <- ! intro_hide_mark
  .

  Theorem correct: ModSemPair.sim MemOpen.MemSem Mem0.MemSem.
  Proof.
   econstructor 1 with (wf:=wf); et; swap 2 3.
    { ss. esplits; ss; et; try refl. hexploit gwf_dummy; i. iRefresh.
      eexists; iRefresh. iSplitP; ss.
      { eexists. rewrite URA.unit_id. refl. }
      ii. econs.
    }

    econs; ss.
    { unfold allocF. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      hide_k. iRefresh.
      do 2 iDestruct SIM. iPure A. iDestruct PRE. iPure PRE. iDestruct A0; cycle 1.
      - iPure A0. des; subst. ss. steps.
        rewrite Any.upcast_downcast in *. clarify. destruct v; ss. clarify.
        rename t into mem_src.
        unhide_k. steps. rewrite Any.upcast_downcast in *. steps.
        force_l. esplits. steps.
        hret_tac SIM (@URA.unit Σ); ss; et.
        { iRefresh. right; iRefresh. rr; ss. esplits; et.
          instantiate (1:=mem_tgt.(Mem.nb) - mem_src.(Mem.nb) + x).
          admit "ez - arith".
        }
        { esplits; ss; et; ss.
          - eexists; iRefresh. iSplitP; et.
        }
      - do 3 iDestruct A0. iMod A0. iMod A1. iDestruct A2. iMod A2. des; subst. ss.
        apply_all_once Any.upcast_inj. des; clarify. steps.
        rewrite Any.upcast_downcast in *. steps.
        astart 0. astop. force_l. esplits; et.
        unhide_k. steps. rewrite Any.upcast_downcast in *. steps.
        hret_tac SIM (@URA.unit Σ); ss; et.
        { iRefresh. left; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss.
          - eexists; iRefresh. iSplitP; ss.
        }
      -
      Idestruct A0.
      (* des. clarify. apply Any.upcast_inj in PRE. des; clarify. *)
      steps. rewrite Any.upcast_downcast in *. steps.
      set (blk := (Mem.nb mem_tgt)). rename x into sz. rename x0 into delta. rename x1 into mem_src0.

      astart 0. astop.

      eapply own_upd in SIM; cycle 1; [|rewrite intro_iHyp in SIM; iMod SIM].
      { eapply GRA.embed_updatable.
        eapply Auth.auth_alloc2.
        instantiate (1:=(_points_to (blk + delta, 0%Z) (repeat (Vint 0) sz))).
        (* instantiate (1:=(fun _b _ofs => if (dec _b blk) && ((0 <=? _ofs) && (_ofs <? Z.of_nat sz))%Z then inl (Some (Vint 0)) else inr tt)). *)
        iOwnWf SIM. iRefresh.
        clear - WF WFTGT A.
        ss. do 2 ur. ii. rewrite unfold_points_to. des_ifs.
         - bsimpl. des. des_sumbool. subst. hexploit (A (blk + delta) k0); et. intro T. inv T; [|eq_closure_tac].
           + exploit WFTGT; et. i; des. lia.
           + rewrite URA.unit_idl. Ztac. rewrite repeat_length in *. rewrite Z.sub_0_r. rewrite repeat_nth_some; [|lia]. ur. ss.
         - rewrite URA.unit_id. do 2 eapply lookup_wf. eapply GRA.embed_wf in WF. des. eapply Auth.black_wf; et.
      }
      rewrite <- GRA.embed_add in SIM. rewrite own_sep in SIM. iDestruct SIM.

      force_l. eexists. hret_tac SIM A0.
      - split; [|refl]; iRefresh. eexists; iRefresh. iSplitP; ss.
      - cbn. esplits; et.
        + eexists; iRefresh. iSplitL SIM; et. ii.
          destruct (mem_tgt.(Mem.cnts) (blk + delta) ofs) eqn:T.
          { exfalso. exploit WFTGT; et. i; des. lia. }
          ss. do 2 ur.
          exploit A; et. rewrite T. intro U. inv U. rewrite unfold_points_to. ss. rewrite repeat_length.
          destruct (dec b (blk + delta)); subst; ss.
          * unfold update. des_ifs_safe. rewrite <- H0. rewrite URA.unit_idl. des_ifs.
            { rewrite Z.sub_0_r. bsimpl. des. Ztac. rewrite repeat_nth_some; try lia. econs. }
            { econs. }
          * rewrite URA.unit_id. unfold update. des_ifs.
        + clear - WFTGT. i. ss. unfold update in *. des_ifs. exploit WFTGT; et. i. des. lia.
    }
    econs; ss.
    { unfold freeF. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *. ss.
      iRefresh. do 3 iDestruct PRE. iPure PRE. iPure A. clarify. apply Any.upcast_inj in PRE. des; clarify.
      do 2 iDestruct SIM. iPure A.
      steps. rewrite Any.upcast_downcast in *. steps.

      astart 0. astop.

      rename n into b. rename z into ofs. rename x0 into mem_src0. rename x into v.
      iMerge SIM A0. rewrite <- own_sep in SIM. rewrite GRA.embed_add in SIM.
      iOwnWf SIM. eapply GRA.embed_wf in WF; des.
      assert(HIT: mem_src0 b ofs = (Some v)).
      { clear - WF.
        dup WF. eapply Auth.auth_included in WF. des. eapply pw_extends in WF. eapply pw_extends in WF.
        rewrite _points_to_hit in WF.
        eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
      }
      set (mem_src1 := fun _b _ofs => if dec _b b && dec _ofs ofs then (ε: URA.car (t:=Excl.t _)) else mem_src0 _b _ofs).
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
        eapply Auth.auth_dealloc.
        instantiate (1:=mem_src1).
        clear - WF'.

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
          specialize (H0 b ofs). rewrite _points_to_hit in H0. eapply Excl.wf in H0. des; ss.
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
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *. ss.
      iRefresh. do 2 iDestruct PRE. iPure PRE. iPure A. clarify. apply Any.upcast_inj in PRE. des; clarify.
      do 2 iDestruct SIM. iPure A.
      steps. rewrite Any.upcast_downcast in *. steps.

      astart 0. astop.
      rename n into b. rename z into ofs. rename x into mem_src0.
      iMerge SIM A0. rewrite <- own_sep in SIM. rewrite GRA.embed_add in SIM. iOwnWf SIM.
      assert(T: mem_src0 b ofs = (Some v)).
      { clear - WF.
        apply GRA.embed_wf in WF. des; ss. dup WF.
        eapply Auth.auth_included in WF. des.
        eapply pw_extends in WF. eapply pw_extends in WF. rewrite _points_to_hit in WF.
        des; ss. eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
      }
      exploit A; et. intro U. rewrite T in U. inv U; ss. unfold Mem.load.
      rewrite <- GRA.embed_add in SIM. rewrite own_sep in SIM. iDestruct SIM.
      force_r; ss. clarify. steps. force_l. esplits.
      hret_tac SIM A0.
      { split; [|refl]; ss; iRefresh. iSplitP; ss. }
      { ss. esplits; eauto. eexists; iRefresh. iSplitP; ss; et. }
    }
    econs; ss.
    { unfold storeF. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *. ss.
      iRefresh. do 3 iDestruct PRE. iPure PRE. iPure A. clarify. apply Any.upcast_inj in PRE. des; clarify.
      do 2 iDestruct SIM. iPure A.
      steps. rewrite Any.upcast_downcast in *. steps. ss. clarify.

      astart 0. astop.
      rename n0 into b. rename z0 into ofs. rename x0 into mem_src0. rename x into v0. rename v into v1.
      iMerge SIM A0. rewrite <- own_sep in SIM. rewrite GRA.embed_add in SIM. iOwnWf SIM.
      assert(T: mem_src0 b ofs = (Some v0)).
      { clear - WF.
        apply GRA.embed_wf in WF. des; ss. dup WF.
        eapply Auth.auth_included in WF. des.
        eapply pw_extends in WF. eapply pw_extends in WF. rewrite _points_to_hit in WF.
        des; ss.
        eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
      }
      exploit A; et. intro U. rewrite T in U. inv U; ss. unfold Mem.store. des_ifs. steps.
      set (mem_src1 := fun _b _ofs => if dec _b b && dec _ofs ofs then (Some v1: URA.car (t:=Excl.t _)) else mem_src0 _b _ofs).
      eapply GRA.embed_wf in WF; des.
      assert(WF': URA.wf (mem_src1: URA.car (t:=Mem1._memRA))).
      { clear - WF. unfold mem_src1. do 2 ur. ii. eapply URA.wf_mon in WF. ur in WF. des.
        des_ifs; et.
        - bsimpl; des; des_sumbool; subst. ur; ss.
        - do 2 eapply lookup_wf; et.
      }
      eapply own_upd in SIM; cycle 1; [|rewrite intro_iHyp in SIM; iMod SIM].
      { eapply GRA.embed_updatable. eapply Auth.auth_update with (a':=mem_src1) (b':=_points_to (b, ofs) [v1]); et.
        clear - wf WF'. ii. des. subst. esplits; et.
        do 2 ur in WF'. do 2 spc WF'.
        subst mem_src1. ss. des_ifs; bsimpl; des; des_sumbool; ss.
        do 2 ur. do 2 (apply func_ext; i). des_ifs.
        - bsimpl; des; des_sumbool; subst. rewrite _points_to_hit.
          do 2 ur in WF. do 2 spc WF. rewrite _points_to_hit in WF. eapply Excl.wf in WF. rewrite WF. ur; ss.
        - bsimpl; des; des_sumbool; rewrite ! _points_to_miss; et.
      }
      rewrite <- GRA.embed_add in SIM. rewrite own_sep in SIM. iDestruct SIM. fold (points_to (b,ofs) [v1]) in A0.
      force_l. eexists.
      hret_tac SIM A0.
      { split; [|refl]; iRefresh. ss. }
      { ss. esplits; eauto.
        - eexists; iRefresh. iSplitP; ss; et. ii. des_ifs.
          + bsimpl; des; des_sumbool; subst. do 2 spc A. rewrite Heq in *. rewrite T in *.
            unfold mem_src1. rewrite ! dec_true; ss. econs.
          + erewrite f_equal; [apply A|]. unfold mem_src1. des_ifs. bsimpl; des; des_sumbool; subst; ss.
        - ii. ss. des_ifs.
          + bsimpl; des; des_sumbool; subst. eapply WFTGT; et.
          + eapply WFTGT; et.
      }
    }
    econs; ss.
    { unfold cmpF. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *. ss.
      iRefresh. do 2 iDestruct SIM. iPure A. do 2 iDestruct PRE. iPure A0. clarify.
      rename x into mem_src0.
      assert (VALIDPTR: forall b ofs v (WF: URA.wf ((Auth.black (mem_src0: URA.car (t:=Mem1._memRA))) ⋅ ((b, ofs) |-> [v]))),
                 Mem.valid_ptr mem_tgt b ofs = true).
      { clear - A. i. cut (mem_src0 b ofs = Some v).
        - i. unfold Mem.valid_ptr.
          specialize (A b ofs). rewrite H in *. inv A. ss.
        - clear - WF.
          dup WF.
          eapply Auth.auth_included in WF. des.
          eapply pw_extends in WF. eapply pw_extends in WF. rewrite _points_to_hit in WF.
          des; ss.
          eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
      }
      steps. rewrite Any.upcast_downcast in *. steps.
      astart 0. astop.
      Ltac iDestruct H :=
        match type of H with
        | iHyp (Exists _, _) _ => destruct H as [? H]; iRefresh
        | iHyp (_ ** _) _ =>
          let name0 := fresh "A" in
          apply sepconj_split in H as [? [? [H [name0 ?]]]]; subst; iRefresh
        | iHyp (_ ∨ _) _ =>
          let name0 := fresh "A" in
          destruct H as [H|name0]; iRefresh
        end.
      iMerge SIM A1. rewrite <- own_sep in SIM. iOwnWf SIM. rewrite own_sep in SIM. iDestruct SIM.
      iDestruct PRE; cycle 1.
      { iPure A1. des; subst. apply Any.upcast_inj in A1. des; clarify. steps.
        force_l. eexists. hret_tac SIM A0.
        { split; [ss; iRefresh|refl]. iSplitP; ss. }
        { ss. esplits; et. eexists; iRefresh. iSplitP; ss; et. }
      }
      iDestruct PRE; cycle 1.
      { repeat iDestruct A1; subst. iPure A1. iPure A2. iPure A3. subst. apply Any.upcast_inj in A1. des; clarify. steps.
        rewrite GRA.embed_add in WF. eapply GRA.embed_wf in WF; des.
        erewrite VALIDPTR; et. ss. rewrite ! dec_true; ss. steps.
        force_l. eexists. hret_tac SIM A0.
        { split; [ss; iRefresh|refl]. iSplitP; ss. }
        { ss. esplits; et. eexists; iRefresh. iSplitP; ss; et. }
      }
      iDestruct PRE; cycle 1.
      { repeat iDestruct A1; subst. iPure A1. iPure A2. iPure A3. subst. apply Any.upcast_inj in A1. des; clarify. steps.
        rewrite ! GRA.embed_add in WF. eapply GRA.embed_wf in WF; des.
        erewrite VALIDPTR; et; cycle 1.
        { rewrite URA.add_assoc in WF. eapply URA.wf_mon in WF; et. }
        erewrite VALIDPTR; et; cycle 1.
        { rewrite URA.add_comm with (a:=(x6, x7) |-> [x8]) in WF. rewrite URA.add_assoc in WF. eapply URA.wf_mon in WF; et. }
        rewrite URA.add_comm in WF. eapply URA.wf_mon in WF. ur in WF; ss.
        replace (dec x6 x9 && dec x7 x10) with false; cycle 1.
        { clear - WF.
          exploit _points_to_disj; et. intro NEQ.
          des; try (by rewrite dec_false; ss). rewrite dec_false with (x0:=x7); ss. rewrite andb_false_r; ss.
        }
        steps. force_l. eexists. hret_tac SIM A0.
        { split; [ss; iRefresh|refl]. iSplitP; ss. }
        { ss. esplits; et. eexists; iRefresh. iSplitP; ss; et. }
      }
      iDestruct PRE; cycle 1.
      { repeat iDestruct A1; subst. iPure A1. iPure A2. iPure A3. subst. apply Any.upcast_inj in A1. des; clarify. steps.
        rewrite GRA.embed_add in WF. eapply GRA.embed_wf in WF; des.
        erewrite VALIDPTR; et. ss. steps.
        force_l. eexists. hret_tac SIM A0.
        { split; [ss; iRefresh|refl]. iSplitP; ss. }
        { ss. esplits; et. eexists; iRefresh. iSplitP; ss; et. }
      }
      iDestruct PRE; cycle 1.
      { repeat iDestruct PRE; subst. iPure A1. iPure A2. iPure PRE. subst. apply Any.upcast_inj in PRE. des; clarify. steps.
        rewrite GRA.embed_add in WF. eapply GRA.embed_wf in WF; des.
        erewrite VALIDPTR; et. ss. steps.
        force_l. eexists. hret_tac SIM A0.
        { split; [ss; iRefresh|refl]. iSplitP; ss. }
        { ss. esplits; et. eexists; iRefresh. iSplitP; ss; et. }
      }
    }
  Qed.

End SIMMODSEM.
