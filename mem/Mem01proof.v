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

End ALIST.
Arguments alist_pop [K R] {RD_K} [V].
Arguments alist_remove [K R] {RD_K} [V].

Section ILIST.
  Context `{Σ: GRA.t}.

  Definition iPropL := alist string iProp.

  Definition from_iPropL (l: iPropL): iProp :=
    fold_alist (fun _ P acc => P ** acc) (emp)%I l.

  Definition iPropL_merge (Hn0 Hn1: string) (Hn2: string) (l0: iPropL): option iPropL :=
    do '(P0, l1) <- alist_pop Hn0 l0;
    do '(P1, l2) <- alist_pop Hn1 l1;
    Some (alist_add Hn0

                    destruct *
          make pure
               destruct ex
               assert
          /\
          destruct \/
          upd

  Definition Sepconj (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => exists a b, r = URA.add a b /\ P a /\ Q b).
  Definition Pure (P: Prop): iProp' :=
    Seal.sealing
      "iProp"
      (fun _ => P).
  Definition Ex {X: Type} (P: X -> iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => exists x, P x r).
  Definition Univ {X: Type} (P: X -> iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => forall x, P x r).
  Definition Own (r0: Σ): iProp' :=
    Seal.sealing
      "iProp"
      (fun r1 => URA.extends r0 r1).
  Definition And (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => P r /\ Q r).
  Definition Or (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => P r \/ Q r).
  Definition Impl (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => URA.wf r -> P r -> Q r).
  Definition Wand (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r => forall rp, URA.wf (r ⋅ rp) -> P rp -> Q (r ⋅ rp)).
  Definition Upd (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (fun r0 => forall ctx, URA.wf (r0 ⋅ ctx) -> exists r1, URA.wf (r1 ⋅ ctx) /\ P r1).


                    assert
                    split
                    pure
                    destruct *
          destruct \/
          de

    None.

    match exprs with
    | h :: t =>
      do hexp <- (compile_expr h); compile_exprs t (acc ++ [hexp])
    | [] => Some acc
    end
  .

    alist_find




  alist_update

  Definiti

  Definition from_iPropR

  Lemma from_iPropL_split (Pn Qn: string) (P Q: iPropL)

        (l0 ++ P :: l1)


  Fixpoi

  alist _add



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


alist_add


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

    Definition aa: iProp :=
      ((⌜5 = 7⌝ ** ⌜9 = 10⌝)
         **
         (∃ mem_src, (Own (GRA.embed ((Auth.black mem_src): URA.car (t:=Mem1.memRA))))
                       **
                       (⌜forall b ofs, sim_loc ((mem_tgt.(Mem.cnts)) b ofs) (mem_src b ofs)⌝)))%I.

    Definition cc: iProp :=
      (∃ (n: nat), ⌜(n + 1 = 1 + n)%nat⌝)%I.

    Goal bi_entails aa cc.
    Proof.
      unfold aa, cc.
      match goal with
      |  |- bi_entails ?a _ =>
         let tr := parse_iProp_tree a in
         change a with (from_iProp_tree tr)
      end.
      admit "".
    Qed.

    Admitted.
      Show Proof.

      let k := constr:(fun n: nat => ⌜(n = n)⌝ ** ⌜(n = n)⌝%I: iProp) in
      (match type of k with
       | ?A -> bi_car iProp =>
         let khole := eval cbn beta in (k (@hole A)) in
             let tr := parse_iProp_tree khole in
             let fhole := eval pattern (@hole A) in tr in
                 match fhole with
                 | ?f (@hole A) => constr:(@iProp_tree_kop A bi_exist f)
                 end
       end).

      let k := constr:(fun n: nat => ⌜(n = n)⌝ ** ⌜(n = n)⌝%I: iProp) in
      (match type of k with
       | ?A -> bi_car iProp =>
         let khole := eval cbn beta in (k (@hole A)) in
             let tr := parse_iProp_tree khole in
             let a := pattern (@hole A) in tr in
                 match a with
                 | ?f (@hole A) => pose f
                 end
       end).



           in

             admit ""


         uconstr:()

         unshelve epose (_: A -> iProp_tree);
         [
           let tmp := fresh A in
           intros tmp;
           let kp := eval simpl in (k tmp) in
               let tr := parse_iProp_tree kp in
               exact tr
         |
         match goal with
         | [ktr: A -> iProp_tree |- _] =>
           match eval unfold ktr in ktr with
           | ?v => clear ktr; pose (@iProp_tree_kop A bi_exist v)
           end
         end
         ]
       end).

      ) with
           | ?aaa => idtac
             end
             .

      match (let k := constr:(fun n: nat => ⌜(n = n)⌝ ** ⌜(n = n)⌝%I: iProp) in
             (match type of k with
              | ?A -> bi_car iProp =>
                unshelve epose (_: A -> iProp_tree);
                [
                  let tmp := fresh A in
                  intros tmp;
                  let kp := eval simpl in (k tmp) in
                      let tr := parse_iProp_tree kp in
                      exact tr
                |
                match goal with
                | [ktr: A -> iProp_tree |- _] =>
                  match eval unfold ktr in ktr with
                  | ?v => clear ktr; pose (@iProp_tree_kop A bi_exist v); constr:(1)
                  end
                end
                ]
              end)) with
      | ?aaa => idtac
      end
      .

        in pose x.

      Show Proof

      unshelve epose (_: nat -> iProp_tree).
      { intros n.
        let tr := parse_iProp_tree constr:((fun n: nat => ⌜(n = n)⌝ ** ⌜(n = n)⌝%I: iProp) n) in pose tr.


      clear i0.

      Set Printing All.


      clear i.
      pose (fun n: nat => ⌜(n = n)⌝%I: iProp).

      epose (_: nat). := _).

      epose (_: nat -> iProp_tree).
      { intros n.
        match constr:(b n) with
        | ?P =>
          let tr := parse_iProp_tree P in
          exact tr
        end.
      }

        match (b with

      unshelve eauto.


      match constr:(fun n: nat => ⌜(n = n)⌝%I: iProp) with
      | ?k =>
        pose (fun n => k n)
      end.

      pose (fun n: nat => ⌜(n = n)⌝%I: iProp).


      match goal with
      |  |- bi_entails _ ?a =>

         match a with
         | ?op ?k =>
           match type of k with
           | ?A -> ?B =>
             pose k
           end
         end
      end.


    Ltac parse_iProp_tree tr :=
      match tr with
      | ?op (?P0: iProp) (?P1: iProp) =>
        let tr0 := parse_iProp_tree P0 in
        let tr1 := parse_iProp_tree P1 in
        constr:(iProp_tree_binop op tr0 tr1)
      | ?op (?P: iProp) =>
        let tr := parse_iProp_tree P in
        constr:(iProp_tree_unop op tr)
      | ?op (fun x => ?k x) =>
        pose k;
        let ktr := parse_iProp_tree (k x) in
        constr:(iProp_tree_kop op (fun x => ktr))
      | ?P => constr:(iProp_tree_base P)
      end.


      pose (parse_iProp

      change aa with parse_i



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





      ((⌜5 = 7⌝ ** ⌜9 = 10⌝) **
                             (∃ mem_src : nat → Z → Excl.car,
                                 (Own (GRA.embed ((Auth.black mem_src): URA.car (t:=Mem1.memRA)))) **
                                                                                                   ⌜∀ (b : nat) (ofs : Z) (v: option val), sim_loc v (mem_src b ofs)⌝))%I.

  End REFLECT.

  Theorem correct: ModPair.sim Mem1.Mem Mem0.Mem.
  Proof.
    admit "TODO: replace it with Mem0Openproof".
  Qed.

End SIMMODSEM.
