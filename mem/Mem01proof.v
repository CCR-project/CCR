Require Import Mem0 Mem1 HoareDef SimModSem.
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


Module PARSE.
  Section PARSE.
    Context `{Σ: GRA.t}.

    Inductive iProp_tree: Type :=
    | iProp_tree_base (P: iProp)
    | iProp_tree_binop (op: iProp -> iProp -> iProp) (tr0 tr1: iProp_tree)
    | iProp_tree_unop (op: iProp -> iProp) (tr: iProp_tree)
    | iProp_tree_kop A (op: (A -> iProp) -> iProp) (k: A -> iProp_tree)
    .

    Fixpoint from_iProp_tree (tr: iProp_tree): iProp :=
      match tr with
      | iProp_tree_base P => P
      | iProp_tree_binop op P Q => op (from_iProp_tree P) (from_iProp_tree Q)
      | iProp_tree_unop op P => op (from_iProp_tree P)
      | @iProp_tree_kop A op k => op (fun a => from_iProp_tree (k a))
      end.

    Definition hole (A: Type): A. Admitted.

    Ltac parse_iProp_tree p :=
      match p with
      | ?op (?P0: iProp) (?P1: iProp) =>
        let tr0 := parse_iProp_tree P0 in
        let tr1 := parse_iProp_tree P1 in
        constr:(iProp_tree_binop op tr0 tr1)
      | ?op (?P: iProp) =>
        let tr := parse_iProp_tree P in
        constr:(iProp_tree_unop op tr)
      | ?op ?k =>
        match type of k with
        | ?A -> bi_car iProp =>
          let khole := (eval cbn beta in (k (@hole A))) in
          let tr := parse_iProp_tree khole in
          let fhole := (eval pattern (@hole A) in tr) in
          match fhole with
          | ?f (@hole A) => constr:(@iProp_tree_kop A op f)
          end
        end
      | ?P => constr:(iProp_tree_base P)
      end.

    Definition iProp_list := alist string iProp_tree.

    Definition from_iProp_list (l: iProp_list): iProp :=
      fold_alist (fun _ tr acc => from_iProp_tree tr ** acc) (emp)%I l.
  End PARSE.
End PARSE.


Section ALIST.
  Fixpoint alist_pop (K : Type) (R : K → K → Prop) (RD_K : RelDec R) (V : Type)
           (k : K) (m : alist K V): option (V * alist K V) :=
    match m with
    | [] => None
    | (k', v) :: ms =>
      if k ?[R] k'
      then Some (v, ms)
      else match @alist_pop K R RD_K V k ms with
           | Some (v', ms') => Some (v', (k', v) :: ms')
           | None => None
           end
    end.

  Fixpoint alist_pops (K : Type) (R : K → K → Prop) (RD_K : RelDec R) (V : Type)
           (k : list K) (m : alist K V): alist K V * alist K V :=
    match k with
    | [] => ([], m)
    | khd::ktl =>
      let (l, m0) := alist_pops RD_K ktl m in
      match alist_pop RD_K khd m0 with
      | Some (v, m1) => ((khd, v)::l, m1)
      | None => (l, m0)
      end
    end.
End ALIST.
Arguments alist_pop [K R] {RD_K} [V].
Arguments alist_pops [K R] {RD_K} [V].
Arguments alist_remove [K R] {RD_K} [V].

Section ILIST.
  Context `{Σ: GRA.t}.

  Definition iPropL := alist string iProp.

  (* Definition from_iPropL (l: iPropL): iProp := *)
  (*   fold_alist (fun _ P acc => P ** acc) (emp)%I l. *)

  Fixpoint from_iPropL (l: iPropL): iProp :=
    match l with
    | [] => (emp)%I
    | [(_, P)] => P
    | (_, Phd)::Ptl => Phd ** (from_iPropL Ptl)
    end.

  Lemma iPropL_clear Hn (l: iPropL)
    :
      from_iPropL l -∗ from_iPropL (alist_remove Hn l).
  Proof.
  Admitted.

  Lemma iPropL_one Hn (l: iPropL) (P: iProp)
        (FIND: alist_find Hn l = Some P)
    :
      from_iPropL l -∗ P.
  Proof.
  Admitted.

  Lemma iPropL_pure Hn (l: iPropL) (P: Prop)
        (FIND: alist_find Hn l = Some (⌜P⌝)%I)
        (SATISFIABLE: exists r, (from_iPropL l) r)
    :
      P.
  Proof.
  Admitted.

  Lemma iPropL_entails Hn (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn l = Some P0)
        (ENTAIL: P0 -∗ P1)
    :
      from_iPropL l -∗ from_iPropL (alist_add Hn P1 l).
  Proof.
  Admitted.

  Lemma iPropL_destruct_ex Hn (l: iPropL) A (P: A -> iProp)
        (FIND: alist_find Hn l = Some (∃ (a: A), P a)%I)
    :
      from_iPropL l -∗ ∃ (a: A), from_iPropL (alist_add Hn (P a) l).
  Proof.
  Admitted.

  Lemma iPropL_destruct_or Hn (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn l = Some (P0 ∨ P1)%I)
    :
      from_iPropL l -∗ from_iPropL (alist_add Hn P0 l) ∨ from_iPropL (alist_add Hn P1 l).
  Proof.
  Admitted.

  Lemma iPropL_destruct_sep Hn_old Hn_new0 Hn_new1 (l: iPropL) (P0 P1: iProp)
        (FIND: alist_find Hn_old l = Some (P0 ** P1))
    :
      from_iPropL l -∗ from_iPropL (alist_add Hn_new1 P1 (alist_add Hn_new0 P0 (alist_remove Hn_old l))).
  Proof.
  Admitted.

  (* TODO: iPropL_own_merge & iPropL_own_split *)

  Lemma iPropL_upd Hn (l: iPropL) (P: iProp)
        (FIND: alist_find Hn l = Some (#=> P))
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn P l).
  Proof.
  Admitted.

  Lemma iPropL_assert (Hns: list string) (Hn_new: string) (l: iPropL) (P: iProp)
        (FIND: from_iPropL (fst (alist_pops Hns l)) -∗ P)
    :
      from_iPropL l -∗ #=> from_iPropL (alist_add Hn_new P (snd (alist_pops Hns l))).
  Proof.
  Admitted.

  Lemma iPropL_init (Hn: string) (P: iProp)
    :
      P -∗ from_iPropL [(Hn, P)].
  Proof.
  Admitted.

  Lemma current_iprops_own ctx (M: URA.t) `{@GRA.inG M Σ} (m: M)
        (ACC: current_iprops ctx (Own (GRA.embed m)))
    :
      URA.wf m.
  Proof.
  Admitted.
End ILIST.
Arguments from_iPropL: simpl never.

Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  (* Eval compute in (@RA.car (RA.excl Mem.t)). *)
  Eval compute in (@URA.car Mem1._memRA).
  Inductive sim_loc: option val -> URA.car (t:=(Excl.t _)) -> Prop :=
  | sim_loc_present v: sim_loc (Some v) (Some v)
  | sim_loc_absent: sim_loc None ε
  .
  Hint Constructors sim_loc: core.

  Definition mem_tgt: Mem.t. Admitted.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).
  Let wf: W -> Prop :=
    @mk_wf
      _
      Mem.t
      (fun mem_tgt _ => (∃ mem_src, (Own (GRA.embed ((Auth.black mem_src): URA.car (t:=Mem1.memRA))))
                                      **
                                      (⌜forall b ofs, sim_loc ((mem_tgt.(Mem.cnts)) b ofs) (mem_src b ofs)⌝)
                        )%I)
      (fun mem_tgt mp_tgt _ => mp_tgt = mem_tgt↑ /\ forall b ofs v, mem_tgt.(Mem.cnts) b ofs = Some v -> <<NB: b < mem_tgt.(Mem.nb)>>)
  .

  Hint Resolve sim_itree_mon: paco.

  (* Lemma just_wf `{M: RA.t}: forall (x: @RA.car M), RA.wf x -> @URA.wf (of_RA.t M) (URA.of_RA.just x). *)
  (* Proof. i; ss. Qed. *)

  (* Opaque of_RA.t. *)
  (* Opaque URA.auth. *)
  (* Opaque URA.pointwise. *)
  Opaque URA.unit.

  Theorem correct: ModPair.sim Mem1.Mem Mem0.Mem.
  Proof.
    admit "TODO: replace it with Mem0Openproof".
  Qed.

End SIMMODSEM.
