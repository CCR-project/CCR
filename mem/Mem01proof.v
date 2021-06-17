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

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).
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

  Let wf: W -> Prop :=
    @mk_wf
      _ unit
      (fun _ _ _mem_tgt0 =>
         (∃ (mem_tgt0: Mem.t) (memk_src0: URA.car (t:=Mem1._memRA)),
             (⌜(<<TGT: _mem_tgt0 = mem_tgt0↑>>) /\
              (<<SIM: forall b ofs, sim_loc (memk_src0 b ofs) (mem_tgt0.(Mem.cnts) b ofs)>>) /\
              (<<WFTGT: mem_wf mem_tgt0>>)⌝) ∧ (*** TODO: put it inside Mem.t? ***)
             (OwnM ((Auth.black memk_src0): URA.car (t:=Mem1.memRA)))
         )%I)
      top4
  .

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.

  Theorem correct_modsem: forall sk, ModSemPair.sim (SModSem.to_tgt [] (Mem1.SMemSem sk)) (Mem0.MemSem sk).
  Proof.
    admit "".
  Qed.

  Theorem correct: ModPair.sim Mem1.Mem Mem0.Mem.
  Proof.
    econs; ss; et. i. eapply correct_modsem.
  Qed.

End SIMMODSEM.
