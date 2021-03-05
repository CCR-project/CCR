Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef BWMain0 BWMain1 SimModSem.

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
Require Import HTactics.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



Inductive ltac_Wild : Set :=
| ltac_wild : ltac_Wild.
Notation "'__'" := ltac_wild : ltac_scope.
Open Scope ltac_scope.

Ltac r_inb r rs :=
  match rs with
  | r => constr:(true)
  | (r ⋅ ?y) => constr:(true)
  | (?x ⋅ r) => constr:(true)
  | (?x ⋅ ?y) =>
    let tmp0 := r_inb r x in
    let tmp1 := r_inb r y in
    let tmp := eval simpl in (tmp0 || tmp1) in
        (* let tmp := (tmp0 || tmp1) in *)
        constr:(tmp)
  | _ => constr:(false)
  end.

Ltac r_gather Hs :=
  match Hs with
  | (?H0, ?H1) => let rs0 := r_gather H0 in
                  let rs1 := r_gather H1 in
                  constr:((rs0 ⋅ rs1))
  | ?H => match type of H with
          | iHyp _ ?rh => constr:(rh)
          | _ => H
          end
  end.

Ltac r_subtract xs ys :=
  match xs with
  (* | ?x => tryif r_in x ys then constr:(ε) else constr:(x) *)
  | (?xs0 ⋅ ?xs1) =>
    let tmp0 := (r_subtract xs0 ys) in
    let tmp1 := (r_subtract xs1 ys) in
    (* let tmp0 := xs0 in *)
    (* let tmp1 := xs1 in *)
    constr:(tmp0 ⋅ tmp1)
  (* | ?y => (tryif idtac then constr:(ε) else constr:(ε)) *)
  (* | ?y => let tmp := (tryif idtac then constr:(ε) else constr:(ε)) in constr:(tmp) *)
  (* | ?y => constr:(ε) || constr:(ε) *)
  (* | ?y => constr:(if ltac:(r_in y ys) then ε else ε) *)
  (* | ?y => first[constr:(ε)|constr:(ε)] *)
  (* | ?y => constr:(ε) *)
  (* | ?y => constr:(if true then ε else ε) *)
  (* | ?y => let tmp := tryif r_in y ys then constr:(true) else constr:(false) in *)
  (*         constr:(if tmp then ε else ε) *)
  (* | ?y => y *)
  (* | ?y => (r_in y ys; constr:(ε)) + y *)
  | ?y => let tmp := (r_inb y ys) in
          let tmp := constr:(if tmp then ε else y) in
          let tmp := eval simpl in tmp in
              constr:(tmp)
  end
.

Ltac r_clearε rs :=
  match rs with
  | (ε ⋅ ?rs) => let tmp := r_clearε rs in constr:(tmp)
  | (?rs ⋅ ε) => let tmp := r_clearε rs in constr:(tmp)
  | (?rs0 ⋅ ?rs1) =>
    let tmp0 := (r_clearε rs0) in
    let tmp1 := (r_clearε rs1) in
    match tmp0 with
    | ε =>
      match tmp1 with
      | ε => (* constr:(ε) <---- it will give memRA *)
      (* fail 3 *)
        tmp1
      | _ => constr:(tmp1)
      end
    | _ =>
      match tmp1 with
      | ε => constr:(tmp0)
      | _ => constr:(tmp0 ⋅ tmp1)
      end
    end
  | ?r => constr:(r)
  end
.

Ltac r_equalize :=
  match goal with
  | [ |- ?lhs = ?rhs ] =>
    tryif has_evar lhs
    then
      ((tryif has_evar rhs then fail 1 else idtac);
       let tmp0 := (r_subtract rhs lhs) in
       let tmp1 := r_clearε tmp0 in
       instantiate (1:=tmp1))
    else
      ((tryif has_evar rhs then idtac else fail 1);
       let tmp0 := (r_subtract lhs rhs) in
       let tmp1 := r_clearε tmp0 in
       instantiate (1:=tmp1))
  | [ |- URA.extends ?lhs ?rhs ] =>
    let tmp0 := (r_subtract rhs lhs) in
    let tmp1 := r_clearε tmp0 in
    exists tmp1
  (*** match does not work ***)
  (* | [ |- exists _, ?lhs = ?rhs ] => *)
  (*   let tmp := (r_subtract rhs lhs) in *)
  (*   let tmp := r_clearε tmp in *)
  (*   exists tmp *)
  end.

Ltac r_first rs :=
  match rs with
  | (?rs0 ⋅ ?rs1) =>
    let tmp0 := r_first rs0 in
    constr:(tmp0)
  | ?r => constr:(r)
  end
.

(* Ltac r_solver := *)
(*   repeat rewrite <- URA.add_assoc; *)
(*   match goal with *)
(*   (* | [|- (?a ⋅ _) = _ ] => *) *)
(*   (*   repeat (rewrite <- (URA.add_comm a); repeat rewrite URA.add_assoc) *) *)
(*   | [|- (?a ⋅ _) = _ ] => *)
(*     idtac a; *)
(*     repeat rewrite ! URA.add_assoc; *)
(*     rewrite <- (URA.add_comm a); *)
(*     repeat rewrite ! URA.add_assoc; *)
(*     idtac *)
(*     (* repeat (rewrite <- (URA.add_comm a); repeat rewrite URA.add_assoc) *) *)
(*   | [|- ?lhs = ?rhs ] => reflexivity *)
(*   end *)
(* . *)
Ltac r_solve :=
  repeat rewrite URA.add_assoc;
  repeat (try rewrite URA.unit_id; try rewrite URA.unit_idl);
  match goal with
  | [|- ?lhs = (_ ⋅ _) ] =>
    let a := r_first lhs in
    try rewrite <- (URA.add_comm a);
    repeat rewrite <- URA.add_assoc;
    f_equal;
    r_solve
  | _ => reflexivity
  end
.





Section SOLVER.
  Context {Σ: GRA.t}.
  Variables a b c d e f: Σ.

  Goal False.
    let tmp := r_clearε (ε ⋅ ε ⋅ (b ⋅ a) ⋅ ε ⋅ e) in pose tmp as c0.
    assert(c0 = (b ⋅ a) ⋅ e) by reflexivity.
    (* Fail let tmp := r_clearε ((ε ⋅ ε) ⋅ (ε ⋅ ε)) in pose tmp. *)
    let tmp := r_clearε ((ε ⋅ (ε ⋅ ε) ⋅ ε) ⋅ (b ⋅ a) ⋅ ε ⋅ e) in pose tmp as c1.
    assert(c1 = (b ⋅ a) ⋅ e) by reflexivity.
    let tmp := r_clearε ((ε ⋅ ε) ⋅ b ⋅ (ε ⋅ ε) ⋅ a ⋅ ε ⋅ e) in pose tmp as c2.
    assert(c2 = (b ⋅ a) ⋅ e) by reflexivity.
    let tmp := r_clearε (ε ⋅ ε ⋅ (ε ⋅ (ε ⋅ ε ⋅ ε))) in pose tmp as c3.
    assert(c3 = ε) by reflexivity.
  Abort.

  Goal exists x, a ⋅ b = a ⋅ x. eexists. r_equalize; r_solve. Undo 1. symmetry. r_equalize; r_solve. Qed.
  Goal exists x, b ⋅ a = a ⋅ x. eexists. r_equalize; r_solve. Undo 1. symmetry. r_equalize; r_solve. Qed.
  Goal exists x, a ⋅ b = x ⋅ a. eexists. r_equalize; r_solve. Undo 1. symmetry. r_equalize; r_solve. Qed.
  Goal exists x, b ⋅ a = x ⋅ a. eexists. r_equalize; r_solve. Undo 1. symmetry. r_equalize; r_solve. Qed.
  Goal exists x, a = x. eexists. r_equalize; r_solve. Undo 1. symmetry. r_equalize; r_solve. Qed.

  Goal URA.extends (d) (c ⋅ b ⋅ a ⋅ d ⋅ e).
  Proof. r_equalize. r_solve. Qed.

  Goal URA.extends (d) (c ⋅ (b ⋅ a) ⋅ d ⋅ e).
  Proof. r_equalize. r_solve. Qed.

  Goal URA.extends (d ⋅ c ⋅ ε) (ε ⋅ c ⋅ (b ⋅ a) ⋅ d ⋅ e).
  Proof. r_equalize. r_solve. Qed.

  Goal URA.extends (b ⋅ d ⋅ (c ⋅ a) ⋅ e) (a ⋅ ε ⋅ c ⋅ ε ⋅ (b ⋅ ε) ⋅ e ⋅ ε ⋅ d).
  Proof. r_equalize. r_solve. Qed.

  Goal URA.extends ε ε.
  Proof. r_equalize. r_solve. Qed.

  Goal URA.extends a a.
  Proof. r_equalize. r_solve. Qed.

  Goal exists delta, (delta ⋅ d) = (c ⋅ b ⋅ a ⋅ d ⋅ e).
  Proof. eexists. r_equalize. r_solve. Qed.

  Goal exists delta, (c ⋅ b ⋅ a ⋅ d ⋅ e) = (delta ⋅ d).
  Proof. eexists. r_equalize. r_solve. Qed.

  Goal forall (x1 x2 x3 x4 x5: Σ), URA.extends (x4 ⋅ x5 ⋅ (ε ⋅ (x2 ⋅ x3 ⋅ x1))) (x4 ⋅ x5 ⋅ (ε ⋅ (x2 ⋅ x3 ⋅ x1))).
  Proof. i. r_equalize. r_solve. Qed.

  Goal a ⋅ b ⋅ (c ⋅ (d ⋅ e)) = a ⋅ c ⋅ (ε ⋅ (b ⋅ d ⋅ e)).
  Proof. r_solve. Qed.

End SOLVER.


















(******** TODO : remove redundancy with LL01proof ***********)
(* proj1 proj2 *)
(* Definition __gwf_mark__ (* (is_src: bool) *) (P: Prop) (Q: Prop): Prop := P /\ Q. *)
(* Lemma gwf_mark_spec: forall P Q, P /\ Q <-> __gwf_mark__ P Q. refl. Qed. *)
(* (* Opaque __gwf_mark__. *) *)
(* Notation "'☀'" := (__gwf_mark__ _ _) (at level 60). *)

Section MARK.
  Context {Σ: GRA.t}.
  Definition __gwf_mark__ (past cur: Σ): Prop := URA.updatable past cur /\ URA.wf cur.
  Lemma gwf_mark_spec: forall past cur, URA.updatable past cur /\ URA.wf cur <-> __gwf_mark__ past cur. refl. Qed.
  (* Opaque __gwf_mark__. *)
End MARK.
Notation "'☀'" := (__gwf_mark__ _ _) (at level 60).

Ltac on_gwf TAC := match goal with | GWF:☀ |- _ => TAC GWF end.


(* Ltac iCheckWf := *)
(*   tryif (match goal with | [WF0: URA.wf _, WF1: URA.wf _ |- _ ] => idtac end) then fail 1 else idtac *)
(* . *)

(* Ltac iClears' := *)
(*   match goal with *)
(*   | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (([(_, (?src0, _))], ?src1), ?src2) (([(_, (?tgt0, _))], ?tgt1), ?tgt2)) ] => *)
(*     let name := fresh "tmp" in *)
(*     let all := constr:(src0 ⋅ src1 ⋅ tgt0 ⋅ tgt1) in *)
(*     pose all as name; *)
(*     repeat multimatch goal with *)
(*            | [WF: URA.wf ?rh |- _ ] => tryif r_contains rh all then idtac else clear WF *)
(*            | [H: iHyp ?ph ?rh |- _ ] => *)
(*              tryif r_contains rh all then idtac else clear H *)
(*                                                            (* idtac H; *) *)
(*                                                            (*   idtac rh; *) *)
(*                                                            (*   tryif r_contains rh all then idtac "CONTAINS" else idtac "DROP" *) *)
(*            end; *)
(*     clear name *)
(*   end; *)
(*   iCheckWf *)
(* . *)
Ltac iCheckWf :=
  tryif (match goal with | [GWF0: __gwf_mark__ (URA.wf _), GWF1: __gwf_mark__ (URA.wf _) |- _ ] => idtac end) then fail 1 else idtac
  (* tryif (match goal with | [WF0: context[(URA.wf _)], WF1: context[(URA.wf _)] |- _ ] => idtac end) then fail 1 else idtac *)
.

Ltac iClears' :=
  match goal with
  | [ GWF: __gwf_mark__ _ ?cur |- _ ] =>
    repeat multimatch goal with
           | [H: iHyp ?ph ?rh |- _ ] =>
             tryif r_contains rh cur then idtac else clear H
           end
  end;
  iCheckWf.

Ltac iRefresh :=
  clear_bar;
  bar;
  repeat multimatch goal with
         | [H: URA.extends ?a ?b |- _ ] => replace (URA.extends a b) with ((Own a) b) in H by reflexivity
         | [H: iHyp _ _ |- _ ] => revert H
         (*** TODO: move existing resources to top ***)
         (*** TODO: remove redundant URA.wf ***)
         | [H: ?ip ?r |- _ ] =>
           match type of ip with
           | iProp => rewrite intro_iHyp in H; move r at top; move H at bottom
           | _ => idtac
           end
         end;
  i;
  try (match goal with
       | [ |- ?ip ?r ] =>
         match type of ip with
         | iProp => rewrite intro_iHyp
         | _ => idtac
         end
       end);
  try iClears;
  try iClears'
.

Ltac iSplitP :=
  match goal with
  | |- ᐸ (Pure ?ph) ** ?pg ᐳ =>
    erewrite f_equal; cycle 1; [ instantiate (1 := (ε ⋅ _)); rewrite URA.unit_idl; refl | eapply sepconj_merge; iClears ]
  | |- ᐸ ?ph ** (Pure ?pg) ᐳ =>
    erewrite f_equal; cycle 1; [ instantiate (1 := (_ ⋅ ε)); rewrite URA.unit_id; refl | eapply sepconj_merge; iClears ]
  end
.

Ltac iDestruct' H :=
  match type of H with
  | iHyp (Exists _, _) _ => destruct H as [? H]; iRefresh
  | iHyp (_ ** _) _ =>
    let name0 := fresh "A" in
    apply sepconj_split in H as [? [? [H [name0 ?]]]]; subst; iRefresh
  end.

Ltac iSplitL Hs0 :=
  match goal with
  | |- ᐸ ?ph ** ?pg ᐳ =>
    let tmp := (r_gather Hs0) in
    erewrite f_equal; cycle 1; [instantiate (1 := tmp ⋅ _); r_equalize; r_solve|eapply sepconj_merge; iRefresh]
  end.
Ltac iSplitR Hs0 :=
  match goal with
  | |- ᐸ ?ph ** ?pg ᐳ =>
    let tmp := (r_gather Hs0) in
    erewrite f_equal; cycle 1; [instantiate (1 := _ ⋅ tmp); r_equalize; r_solve|eapply sepconj_merge; iRefresh]
  end.

Ltac iExists' Hs := let rs := r_gather Hs in exists rs.



Section AUX.
  Context {Σ: GRA.t}.
  Lemma wf_downward: forall (r0 r1: Σ) (EXT: URA.extends r0 r1), URA.wf r1 -> URA.wf r0.
  Proof.
    i. rr in EXT. des; subst. eapply URA.wf_mon; et.
  Qed.
End AUX.



Ltac iIntro :=
  try on_gwf ltac:(fun GWF => clear GWF); (*** if GWF exists, remove it. otherwise don't ***)
  let A := fresh "A" in
  let wf := fresh "wf" in
  let GWF := fresh "GWF" in
  intros ? wf A; eassert(GWF: ☀) by (split; [refl|exact wf]); iRefresh.
Ltac iSpecialize H G :=
  let rp := r_gather G in
  specialize (H rp); eapply hexploit_mp in H; [|on_gwf ltac:(fun GWF => eapply wf_downward; cycle 1; [by apply GWF|r_equalize; r_solve])];
  specialize (H G); rewrite intro_iHyp in H; clear G; iRefresh
.
Ltac iAssert H Abody :=
  let A := fresh "A" in
  match type of H with
  | iHyp ?Hbody ?rH =>
    match Abody with
    | ltac_wild => eassert(A: iHyp (Hbody -* _) ε)
    | _ => assert(A: iHyp (Hbody -* Abody) ε)
    end;
    [|iSpecialize A H; rewrite URA.unit_idl in A]
  end
.

Ltac iOwnWf G :=
  match goal with
  | H:iHyp (Own ?r) ?rh |- _ =>
    check_equal H G;
    let name := fresh "WF" in
    (* assert(name: URA.wf r); [eapply wf_downward; [eapply H|eapply wf_downward; et; r_equalize; r_solve]|] *)
    assert(name: URA.wf r); [eapply wf_downward; [eapply H|eapply wf_downward; [|on_gwf ltac:(fun GWF => apply GWF)]; r_equalize; r_solve]|]
  end.





Ltac harg_tac :=
  HTactics.harg_tac;
  match goal with
  | [H: URA.wf ?cur |- _] =>
    let name := fresh "GWF" in
    assert(name: __gwf_mark__ cur cur) by (split; [refl|exact H]); clear H
  end.

Ltac hcall_tac x o MR_SRC1 FR_SRC1 RARG_SRC :=
  let mr_src1 := r_gather MR_SRC1 in
  let fr_src1 := r_gather FR_SRC1 in
  let rarg_src := r_gather RARG_SRC in
  (* let tac0 := etrans; [on_gwf ltac:(fun GWF => apply GWF)|eapply URA.extends_updatable; r_equalize; r_solve] in *)
  (* let tac0 := idtac in *)
  let tac0 := etrans; [etrans; [|on_gwf ltac:(fun GWF => apply GWF)]|]; eapply URA.extends_updatable; r_equalize; r_solve; fail in
  let tac1 := (on_gwf ltac:(fun H => clear H);
               let WF := fresh "WF" in
               let tmp := fresh "_tmp_" in
               let GWF := fresh "GWF" in
               intros ? ? ? ? ? WF; cbn in WF; desH WF; subst;
               esplits; ss; et; intros tmp ?; assert(GWF: ☀) by (split; [refl|exact tmp]); clear tmp; iRefresh; iClears') in
  prep;
  match x with
  | ltac_wild =>
    match o with
    | ltac_wild => eapply (hcall_clo _ (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src)); [tac0|lia|..|tac1]
    | _ => eapply (hcall_clo _ (o:=o) (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src)); [tac0|lia|..|tac1]
    end
  | _ => eapply (hcall_clo x (o:=o) (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src)); [tac0|lia|..|tac1]
  end
.

Ltac hret_tac MR_SRC RT_SRC :=
  let mr_src1 := r_gather MR_SRC in
  let fr_src1 := r_gather RT_SRC in
  HTactics.hret_tac mr_src1 fr_src1
.

Section AUX.
  Context `{Σ: GRA.t}.
  Lemma own_update: forall (x y: Σ) rx ctx, URA.updatable x y -> iHyp (Own x) rx -> URA.wf (rx ⋅ ctx) ->
                                            (* exists ry, iHyp (Own y) ry /\ URA.wf (ry ⋅ ctx) /\ URA.updatable rx ry. *)
                                            exists ry, iHyp (Own y) ry /\ URA.wf (ry ⋅ ctx) /\ URA.updatable (rx ⋅ ctx) (ry ⋅ ctx).
  Proof.
    { clear_until Σ. i. dup H. rr in H0. des; subst. r in H.
      specialize (H (ctx0 ⋅ ctx)). rewrite ! URA.add_assoc in H. spc H.
      exists (y ⋅ ctx0). esplits; et.
      - rr. esplits; et.
      - eapply URA.updatable_add; try refl. eapply URA.updatable_add; try refl. et.
    }
  Qed.
  Lemma Own_downward: forall r a0 a1, iHyp (Own r) a0 -> URA.extends a0 a1 -> iHyp (Own r) a1.
  Proof. i. eapply Own_extends; et. Qed.

  (* Lemma is_list_downward: forall ll xs a0 a1, iHyp (is_list ll xs) a0 -> URA.extends a0 a1 -> iHyp (is_list ll xs) a1. *)
  (* Proof. *)
  (*   admit "ez". *)
  (* Qed. *)

  (* Definition updatable_iprop (P Q: iProp): Prop := *)
  (*   forall pr, URA.wf pr -> P pr -> exists qr, Q qr /\ URA.updatable pr qr *)
  (* . *)

  (* Lemma impl_updatable: forall P Q, Impl P Q -> updatable_iprop P Q. *)
  (* Proof. { ii. esplits; eauto. refl. } Qed. *)

  (* Lemma iprop_update: forall (P Q: iProp) rx ctx, updatable_iprop P Q -> iHyp P rx -> URA.wf (rx ⋅ ctx) -> *)
  (*                                                 exists ry, iHyp Q ry /\ URA.wf (ry ⋅ ctx) /\ URA.updatable (rx ⋅ ctx) (ry ⋅ ctx). *)
  (* Proof. { clear_until Σ. i. r in H0. exploit H; try apply H0; et. { eapply URA.wf_mon; et. } i; des. esplits; eauto. *)
  (*          eapply URA.updatable_add; et. refl. } Qed. *)




  (* Lemma upd_update: forall (ctx: Σ) (P: iProp) r0, *)
  (*     iHyp ( |=> P) r0 -> URA.wf (r0 ⋅ ctx) -> *)
  (*     exists r1, iHyp P r1 /\ URA.wf (r1 ⋅ ctx) /\ URA.updatable (r0 ⋅ ctx) (r1 ⋅ ctx). *)
  (* Proof. ii. rr in H. exploit H; et. i; des. esplits; et. eapply URA.updatable_add; try refl. clear - H. r. i. exploit H; et. i; des. esplits; et. Qed. *)

  Lemma upd_update: forall (ctx: Σ) (P: iProp) r0,
      iHyp (Upd P) r0 -> URA.wf (r0 ⋅ ctx) ->
      exists r1, iHyp P r1 /\ URA.wf (r1 ⋅ ctx) /\ URA.updatable (r0 ⋅ ctx) (r1 ⋅ ctx).
  Proof. ii. rr in H. des. eexists r1. exploit H; et. i; des. esplits; et. eapply URA.updatable_add; try refl. clear - H. r. i. exploit H; et. i; des. esplits; et. Qed.

  Lemma unfold_APC: forall n, _APC n =
    match n with
    | 0 => Ret tt
    | S n => break <- trigger (Choose _);;
             if break: bool
             then Ret tt
             else '(fn, varg) <- trigger (Choose _);;
                  trigger (hCall true fn varg);; _APC n
    end.
    { i. destruct n; ss. }
  Qed.

  Ltac bring_front r0 :=
    repeat rewrite URA.add_assoc in *;
    (*** corner case: goal is pure \/ probably already sorted ***)
    try rewrite (URA.add_comm _ r0) in *;
    repeat rewrite URA.add_assoc in *;

    (*** somehow, * does not work well in GWF. WHY??? TODO: FIXME ***)
    on_gwf ltac:(fun GWF =>
                   repeat rewrite URA.add_assoc in GWF;
                   try rewrite (URA.add_comm _ r0) in GWF;
                   repeat rewrite URA.add_assoc in GWF) (*** probably already sorted; so "try" ***)
  .
  Goal forall (a b c d e: Σ), __gwf_mark__ ε (d ⋅ c) -> a ⋅ (b ⋅ c) ⋅ (d ⋅ e) = ε.
    i. bring_front d. bring_front c.
    match goal with | |- ?G => match G with | c ⋅ d ⋅ a ⋅ b ⋅ e = ε => idtac | _ => fail end end.
  Abort.

  Goal forall (a b c d e f: Σ), __gwf_mark__ (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)) (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)) -> a ⋅ (b ⋅ c) ⋅ (d ⋅ e) = f.
    i. bring_front d. bring_front c.
    match goal with | |- ?G => match G with | c ⋅ d ⋅ a ⋅ b ⋅ e = f => idtac | _ => fail end end.
    match goal with | [H: __gwf_mark__ ?rs0 ?rs1 |- _ ] => match rs0 with | (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
    match goal with | [H: __gwf_mark__ ?rs0 ?rs1 |- _ ] => match rs1 with | (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
  Abort.

  Goal forall (a b c d e f: Σ), __gwf_mark__ ε (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)) -> a ⋅ (b ⋅ c) ⋅ (d ⋅ e) = f.
    i. bring_front d. bring_front c.
    match goal with | |- ?G => match G with | c ⋅ d ⋅ a ⋅ b ⋅ e = f => idtac | _ => fail end end.
    match goal with | [H: __gwf_mark__ ?rs0 ?rs1 |- _ ] => match rs0 with | ε => idtac | _ => fail end end.
    match goal with | [H: __gwf_mark__ ?rs0 ?rs1 |- _ ] => match rs1 with | (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
  Abort.

  Ltac iMerge A0 A1 :=
    match type of A0 with
    | iHyp ?p0 ?r0 =>
      match type of A1 with
      | iHyp ?p1 ?r1 =>
        bring_front r1; bring_front r0;

        let ttmp := fresh "ttmp" in
        rename A0 into ttmp;
        assert(A0: iHyp (p0 ** p1) (r0 ⋅ r1)) by (apply sepconj_merge; try assumption);
        clear ttmp; clear A1;

        let tmp := fresh "tmp" in
        let tmpH := fresh "tmpH" in
        (* remember (r0 ⋅ r1) as tmp eqn:tmpH in *; *)
        set (tmp:= r0 ⋅ r1) in *;
        (* remember (r0 ⋅ r1) as tmp eqn:tmpH; *)
        match goal with
        | [GWF: (__gwf_mark__ ?past ?cur) |- _] =>
          match past with
          | cur => unfold tmp in GWF at 1
          | _ =>
            (* idtac past; idtac cur; idtac tmp; idtac r0; idtac r1 ; *)
            (*** corner case: past may or may not contain r0 ⋅ r1 ***)
            remember cur as ttttmp in GWF;
            try unfold tmp in GWF at 1;
            subst ttttmp
            (* remember past as ttttmp in GWF; *)
            (* unfold tmp in GWF at 1; *)
            (* subst ttttmp *)
          end
          (* let ttttmp := fresh "ttttmp" in *)
          (* (* idtac r0; idtac r1; idtac past; idtac cur; idtac tmpH; *) *)
          (* (* let ty := (type of tmpH) in idtac ty; *) *)
          (* remember cur as ttttmp; *)
          (* unfold tmp in GWF; *)
          (* (* rewrite tmpH in GWF; *) *)
          (* subst ttttmp *)
        end;
        clearbody tmp
        (* clear tmpH *)


        (* on_gwf ltac:(fun GWF => rewrite tmpH in GWF at 1); *)
      end
    end.

  Goal forall P Q, iHyp (P -* Q -* P ** Q) ε.
    i. do 2 iIntro. rewrite URA.unit_idl. (*** TODO: How can we remove this?
I needed to write this because "ss" does not work. create iApply that understands r_clearε? ***)
    iMerge A0 A.
    iDestruct' A0.
    (* r in GWF. r in A0. r in A. r. *)
    iMerge A A0.
    ss.
  Qed.

  Goal forall P Q, iHyp (P -* Q -* P ** Q) ε.
    i. do 2 iIntro. rewrite URA.unit_idl.
    iMerge A A0.
    (* r in A. r. r in GWF. *)
    iDestruct' A.
    (* r in A. r in A0. r. r in GWF. *)
    (***
  GWF : URA.updatable (rp ⋅ rp0 ⋅ ε) (x ⋅ x0 ⋅ ε) /\ URA.wf (x ⋅ x0 ⋅ ε)
  ㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡ : IPROPS
  A : P x
  A0 : Q x0
  ============================
  (P ** Q) (x ⋅ x0) ***)
    iMerge A0 A.
    (* r in A0. r. r in GWF. *)
  (* GWF : URA.updatable (rp ⋅ rp0 ⋅ ε) (x0 ⋅ x ⋅ ε) /\ URA.wf (x0 ⋅ x ⋅ ε) *)
  (* ㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡ : IPROPS *)
  (* A0 : (Q ** P) tmp *)
  (* ============================ *)
  (* (P ** Q) tmp *)
    iDestruct' A0.
    iSplit A A0; ss; try r_solve.
  Qed.

  Context `{@GRA.inG BW1.bwRA Σ}.

End AUX.
Global Opaque _APC.



Ltac iUpdate H :=
  eapply upd_update in H; [|on_gwf ltac:(fun GWF => eapply wf_downward; [|eapply GWF]); eexists ε; r_equalize; r_solve; fail];
  let GWF := fresh "GWF" in
  let wf := fresh "WF" in
  let upd := fresh "UPD" in
  destruct H as [? [H [wf upd]]];
  on_gwf ltac:(fun _GWF => eassert(GWF: ☀) by
                   (split; [etrans; [apply _GWF|etrans; [|apply upd]]; eapply URA.extends_updatable; r_equalize; r_solve; fail|exact wf]);
                           clear wf upd; iRefresh; clear _GWF).

Ltac until_bar TAC :=
  (on_last_hyp ltac:(fun id' =>
                       match type of id' with
                       | IPROPS => intros
                       | _ => TAC id'; revert id'; until_bar TAC
                       end)).

Ltac rr_until_bar := until_bar ltac:(fun H => rr in H).








Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG BW1.bwRA Σ}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ) (n: Z),
        (<<SRC: mrps_src0 = Maps.add "Main" (mr, tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "Main" (ε, n↑) Maps.empty>>)
  .

  Opaque URA.unit.

  Theorem correct: ModSemPair.sim BWMain1.MainSem BWMain0.MainSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. unfold alist_add; cbn. esplits; ss; eauto. }

    Opaque URA.add.
    econs; ss.
    { unfold main_body, mainF, ccall, hcall. init.
      harg_tac. des. subst. rewrite Any.upcast_downcast. ss.
      iRefresh. iDestruct PRE. iPure A. clarify. steps.
      unfold interp_hCallE_tgt. steps.
      replace (find (fun '(_fn, _) => dec "getbool" _fn) (ClientStb ++ MainStb)) with
          (Some ("getbool", (mk_simple "Client"
                                       (fun (_: unit) _ o =>
                                          iHyp (⌜True⌝))
                                       (fun _ _ =>
                                          iHyp (⌜True⌝))))).
      2: { unfold ClientStb, MainStb. unseal "stb". ss. }
      steps. rewrite Any.upcast_downcast. ss. steps.
      hcall_tac tt ord_top (@URA.unit Σ) PRE (@URA.unit Σ); ss.
      { esplits; eauto. }
      des; clarify. steps. rewrite Any.upcast_downcast in *. ss. clarify. steps.
      unfold APC, TODO.unbool. des_ifs; ss.
      { steps. force_l. exists 2. steps. rewrite unfold_APC. steps. force_l. exists false.
        steps. force_l. eexists ("get", Any.upcast []). steps.
  Admitted.

End SIMMODSEM.
