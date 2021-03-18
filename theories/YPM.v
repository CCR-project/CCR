Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Export Logic.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.
Set Typeclasses Depth 5.


(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*************************************** YPM *************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)

Section IPM.
  Context {Σ: GRA.t}.
  Definition iHyp (P: Σ -> Prop) (r: Σ): Prop := P r.

  Lemma intro_iHyp: forall P r, P r = iHyp P r.
    { i. unfold iHyp. apply prop_ext. split; i; des; et. }
  Qed.

  Definition IPROPS: Prop := forall x, x - x = 0.

  Lemma IPROPS_intro: IPROPS. r. i. rewrite Nat.sub_diag. ss. Qed.

  Definition __gwf_mark__ (past cur: Σ): Prop := URA.updatable past cur /\ URA.wf cur.
  Lemma gwf_mark_spec: forall past cur, URA.updatable past cur /\ URA.wf cur <-> __gwf_mark__ past cur. refl. Qed.
  (* Opaque __gwf_mark__. *)
  Lemma gwf_update_cur: forall past cur0 cur1, cur0 = cur1 -> __gwf_mark__ past cur0 -> __gwf_mark__ past cur1. i. subst. eauto. Qed.
  Lemma gwf_dummy: (__gwf_mark__ ε ε). Proof. split; try refl. apply URA.wf_unit. Qed.

End IPM.

Notation "'ᐸ' P 'ᐳ'" := (iHyp P _) (at level 60).
Notation "'☀'" := (__gwf_mark__ _ _) (at level 60).
Ltac on_gwf TAC := match goal with | GWF:☀ |- _ => TAC GWF end.

Ltac to_bar TAC :=
  match goal with
  | [H: IPROPS |- _ ] => TAC H
  | _ => idtac
  end.

Ltac bar :=
  to_bar ltac:(fun _ => fail 1);
  let NAME := fresh "ㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡ" in
  assert (NAME : IPROPS) by (exact IPROPS_intro)
.

Goal False.
  bar. clear_tac. Fail bar.
Abort.

Ltac clear_bar := to_bar ltac:(fun H => clear H).

(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*************************************** RESOURCE TACTICS ************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)

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
          | _ => H (*** this is for ε ***)
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

Ltac r_bring_front H r0 :=
  repeat rewrite URA.add_assoc in H;
  try rewrite (URA.add_comm _ r0) in H; (*** probably already sorted; so "try" ***)
  repeat rewrite URA.add_assoc in H;

  (*** the merged one should be in "cur" of GWF ***)
  (* match goal with *)
  (* | GWF: __gwf_mark__ ?past ?cur |- _ => *)

  (* end. *)
  on_gwf ltac:(fun GWF =>
                 erewrite f_equal in GWF; [|repeat rewrite URA.add_assoc;
                                            try rewrite (URA.add_comm _ r0); (*** probably already sorted; so "try" ***)
                                            repeat rewrite URA.add_assoc; refl]; match goal with | bar: IPROPS |- _ => move GWF after bar end);

  (***
(1) Goal is iProp --> should merge in the goal too; otherwise merged one will be cleared later
(2) Goal is sim ----> should not merge in the goal; (mr + fr) should match with "past" of GWF, but this property gets broken
   ***)
  match goal with
  | [ |- (gpaco3 (SimModSem._sim_itree _) _ _ _ _ _  _) ] => idtac
  (* | [ |- iHyp _ _ ] => *)
  (*   repeat rewrite URA.add_assoc; *)
  (*   (*** corner case: goal is pure \/ probably already sorted ***) *)
  (*   try rewrite (URA.add_comm _ r0); (*** probably already sorted; so "try" ***) *)
  (*   repeat rewrite URA.add_assoc *)
  | _ =>
    repeat rewrite URA.add_assoc;
    (*** corner case: goal is pure \/ probably already sorted ***)
    try rewrite (URA.add_comm _ r0); (*** probably already sorted; so "try" ***)
    repeat rewrite URA.add_assoc
  end
.
Ltac r_merge H r0 r1 :=
  r_bring_front H r1; r_bring_front H r0;

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
.

Ltac r_length ls :=
  match ls with
  | (?x ⋅ ?y) =>
    let xl := r_length x in
    let yl := r_length y in
    constr:(xl + yl)
  | _ => constr:(1)
  end.

Ltac r_in r0 rs :=
  match r0 with
  | (@URA.unit _) => idtac
  | _ =>
    match rs with
    | r0 => idtac
    | (r0 ⋅ ?y) => idtac
    | (?x ⋅ r0) => idtac
    | (?x ⋅ ?y) => r_in r0 x + r_in r0 y
    | _ => fail
    end
  end.

Ltac r_contains xs ys :=
  match xs with
  | (?x0 ⋅ ?x1) => r_contains x0 ys; r_contains x1 ys
  | _ => r_in xs ys
  end.

Section RTEST.
  Context {Σ: GRA.t}.
  Let GURA := GRA.to_URA Σ.
  Local Existing Instance GURA. (*********** TODO: remove it; put GRA.to_URA as a coercion and adjust priority ********)
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

  Goal URA.extends ε (ε: Σ).
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

  Goal forall (GWF: __gwf_mark__ ε (d ⋅ c)), iHyp ⌜True⌝ (d ⋅ c) -> iHyp ⌜True⌝ (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)).
    i. bar. r_bring_front H1 d. r_bring_front H1 c.
    match goal with | |- ?G => match G with | iHyp _ (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
  Abort.

  Goal forall (GWF: __gwf_mark__ (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)) (a ⋅ (b ⋅ c) ⋅ (d ⋅ e))), iHyp ⌜True⌝ ((a ⋅ d) ⋅ (c ⋅ b)) -> iHyp ⌜True⌝ (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)).
    i. bar. r_bring_front H d. r_bring_front H c.
    match goal with | |- ?G => match G with | iHyp _ (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
    match goal with | [H: __gwf_mark__ ?rs0 ?rs1 |- _ ] => match rs0 with | (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)) => idtac | _ => fail end end.
    match goal with | [H: __gwf_mark__ ?rs0 ?rs1 |- _ ] => match rs1 with | (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
    match type of H with | iHyp _ ?rs => match rs with | (c ⋅ d ⋅ a ⋅ b) => idtac | _ => fail end end.
  Abort.

  Goal forall (GWF: __gwf_mark__ ε (a ⋅ (b ⋅ c) ⋅ (d ⋅ e))), iHyp ⌜True⌝ ((a ⋅ d) ⋅ (c ⋅ b)) -> iHyp ⌜True⌝ (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)).
    i. bar. r_bring_front H d. r_bring_front H c.
    match goal with | |- ?G => match G with | iHyp _ (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
    match goal with | [H: __gwf_mark__ ?rs0 ?rs1 |- _ ] => match rs0 with | ε => idtac | _ => fail end end.
    match goal with | [H: __gwf_mark__ ?rs0 ?rs1 |- _ ] => match rs1 with | (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
    match type of H with | iHyp _ ?rs => match rs with | (c ⋅ d ⋅ a ⋅ b) => idtac | _ => fail end end.
  Abort.

End RTEST.

(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*************************************** YPM TACTICS *****************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)

Ltac iCheckWf :=
  tryif (match goal with | [GWF0: __gwf_mark__ (URA.wf _), GWF1: __gwf_mark__ (URA.wf _) |- _ ] => idtac end) then fail 1 else idtac
  (* tryif (match goal with | [WF0: context[(URA.wf _)], WF1: context[(URA.wf _)] |- _ ] => idtac end) then fail 1 else idtac *)
.

Ltac iClears := match goal with
                | [ |- iHyp _ ?rgoal ] =>
                  repeat multimatch goal with
                         | [ H: iHyp _ ?r |- _ ] =>
                           tryif r_contains r rgoal
                           then idtac
                           else clear H
                         end
                end.

Ltac iClears' :=
  match goal with
  | [ GWF: __gwf_mark__ _ ?cur |- _ ] =>
    repeat multimatch goal with
           | [H: iHyp ?ph ?rh |- _ ] =>
             tryif r_contains rh cur then idtac else clear H
           end
  end;
  iCheckWf.

Ltac iAlignResource :=
  all_once_fast ltac:(fun H => let ty := (type of H) in
                               match ty with
                               | URA.car => move H at top
                               | _ => idtac
                               end).

Ltac iGuard :=
  match goal with
  | GWF: (__gwf_mark__ ?past ?cur) |- _ =>
    all_once_fast ltac:(fun H => match (type of H) with
                                 | iHyp _ (_ ⋅ _) => fail 3
                                 | iHyp _ (@URA.unit _) => fail 3
                                 | iHyp _ ?r => tryif r_in r cur then idtac else fail 3
                                 | _ => idtac
                                 end)
  end.
Ltac iGuard' :=
  match goal with
  | [GWF: (__gwf_mark__ ?past _) |- _ ] =>
    match goal with
    | [ |- (gpaco3 (SimModSem._sim_itree _) _ _ _ _ (([(_, (?mr, _))], ?fr), _)  _) ] =>
      tryif r_contains past (mr ⋅ fr)
      then idtac
      else fail 2
    | _ => idtac
    end
  end
.
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
  try iClears';
  iAlignResource;
  iGuard; iGuard'
.

Ltac until_bar TAC :=
  (on_last_hyp ltac:(fun id' =>
                       match type of id' with
                       | IPROPS => intros
                       | _ => TAC id'; revert id'; until_bar TAC
                       end)).

Ltac rr_until_bar := until_bar ltac:(fun H => rr in H).
Ltac r_until_bar := until_bar ltac:(fun H => r in H).

(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*************************************** LOGIC TACTICS ***************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)
(*********************************************************************************************************)

Section FACTS.
  Context {Σ: GRA.t}.
  Lemma wf_split: forall (a b: Σ), URA.wf (a ⋅ b) -> URA.wf a /\ URA.wf b.
    { i. split; eapply URA.wf_mon; et. rewrite URA.add_comm; et. }
  Qed.

  Lemma sepconj_merge: forall (a b: Σ) (Pa Pb: iProp), iHyp Pa a -> iHyp Pb b -> iHyp (Pa ** Pb) (a ⋅ b).
  Proof. i. rr. esplits; eauto. Qed.

  Lemma sepconj_split: (forall (ab : Σ) (Pa Pb : iProp), iHyp (Pa ** Pb) (ab) -> exists a b, iHyp Pa a /\ iHyp Pb b /\ ab = a ⋅ b).
    { clear - Σ. ii. unfold iHyp in *. r in H. destruct H. des. esplits; et. }
  Qed.

  Lemma wf_downward: forall (r0 r1: Σ) (EXT: URA.extends r0 r1), URA.wf r1 -> URA.wf r0.
  Proof.
    i. rr in EXT. des; subst. eapply URA.wf_mon; et.
  Qed.

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
  (* Lemma Own_downward: forall r a0 a1, iHyp (Own r) a0 -> URA.extends a0 a1 -> iHyp (Own r) a1. *)
  (* Proof. i. eapply Own_extends; et. Qed. *)

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

End FACTS.

Ltac iApply H := erewrite f_equal; [apply H|r_solve].

(* Ltac iSplit Hs0 Hs1 := *)
(*   match goal with *)
(*   | [ |- iHyp (?ph ** ?pg) _ ] => *)
(*     let tmp0 := (r_gather Hs0) in *)
(*     let tmp1 := (r_gather Hs1) in *)
(*     erewrite f_equal; cycle 1; [instantiate (1:= tmp0 ⋅ tmp1)|eapply sepconj_merge; iClears] *)
(*   end *)
(* . *)

Ltac iPure H := rr in H; to_bar ltac:(fun BAR => move H after BAR). (* ; iRefresh. *)

Ltac iSplitP :=
  match goal with
  | |- ᐸ (Pure ?ph) ** ?pg ᐳ =>
    erewrite f_equal; cycle 1; [ instantiate (1 := (ε ⋅ _)); rewrite URA.unit_idl; refl | eapply sepconj_merge; iClears ]
  | |- ᐸ ?ph ** (Pure ?pg) ᐳ =>
    erewrite f_equal; cycle 1; [ instantiate (1 := (_ ⋅ ε)); rewrite URA.unit_id; refl | eapply sepconj_merge; iClears ]
  end
.

Ltac iDestruct H :=
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
Ltac iIntro :=
  try on_gwf ltac:(fun GWF => clear GWF); (*** if GWF exists, remove it. otherwise don't ***)
  let A := fresh "A" in
  let wf := fresh "wf" in
  let GWF := fresh "GWF" in
  intros ? wf A; eassert(GWF: ☀) by (split; [refl|exact wf]); clear wf; iRefresh.

Ltac iOwnWf G :=
  match goal with
  | H:iHyp (Own ?r) ?rh |- _ =>
    check_equal H G;
    let name := fresh "WF" in
    (* assert(name: URA.wf r); [eapply wf_downward; [eapply H|eapply wf_downward; et; r_equalize; r_solve]|] *)
    assert(name: URA.wf r); [eapply wf_downward; [eapply H|eapply wf_downward; [|on_gwf ltac:(fun GWF => apply GWF)]; r_equalize; r_solve]|]
  end.
Ltac iMerge A0 A1 :=
  match type of A0 with
  | iHyp ?p0 ?r0 =>
    match type of A1 with
    | iHyp ?p1 ?r1 =>
      let ttmp := fresh "ttmp" in
      rename A0 into ttmp;
      assert(A0: iHyp (p0 ** p1) (r0 ⋅ r1)) by (apply sepconj_merge; try assumption);
      clear ttmp; clear A1;
      r_merge A0 r0 r1
    end
  end.
Ltac iSpecialize H G :=
  let rh := r_gather H in
  let rp := r_gather G in
  specialize (H rp); eapply hexploit_mp in H; [|on_gwf ltac:(fun GWF => eapply wf_downward; cycle 1; [by apply GWF|r_equalize; r_solve])];
  specialize (H G); rewrite intro_iHyp in H; clear G;
  r_merge H rh rp; iRefresh
.
Ltac iAssert H Abody :=
  let A := fresh "A" in
  match type of H with
  | iHyp ?Hbody ?rH =>
    match Abody with
    | ltac_wild => eassert(A: iHyp (Hbody -* _) ε)
    | _ => assert(A: iHyp (Hbody -* Abody) ε)
    end;
    [|on_gwf ltac:(fun GWF => rewrite <- URA.unit_id in GWF; set (my_r:=ε) in GWF, A; clearbody my_r);
     iSpecialize A H]
  end
.
Ltac iUpdate H :=
  eapply upd_update in H; [|on_gwf ltac:(fun GWF => eapply wf_downward; [|eapply GWF]); eexists ε; r_equalize; r_solve; fail];
  let GWF := fresh "GWF" in
  let wf := fresh "WF" in
  let upd := fresh "UPD" in
  destruct H as [? [H [wf upd]]];
  on_gwf ltac:(fun _GWF => eassert(GWF: ☀) by
                   (split; [etrans; [apply _GWF|etrans; [|apply upd]]; eapply URA.extends_updatable; r_equalize; r_solve; fail|exact wf]);
                           clear wf upd; iRefresh; clear _GWF).

Ltac iImpure H := let name := fresh "my_r" in
                  specialize (H ε URA.wf_unit I); rewrite intro_iHyp in H;
                  on_gwf ltac:(fun GWF => rewrite <- URA.unit_id in GWF; set (name:=ε) in GWF, H; clearbody name).
Ltac iMod H :=
  match type of H with
  | Impure _ => iImpure H
  | iHyp (⌜ _ ⌝) _ => iPure H
  | iHyp ( |=> _ ) _ => iUpdate H
  | _ => fail
  end
.

Section LTEST.
  Context {Σ: GRA.t}.
  Goal forall (a b c: Σ), False.
    i.
    let n := r_length (a ⋅ b ⋅ c) in pose n.

    (r_in a (a ⋅ b ⋅ c)).
    (r_in b (a ⋅ b ⋅ c)).
    (r_in c (a ⋅ b ⋅ c)).
    (r_in a (a ⋅ b)).
    (r_in b (a ⋅ b)).
    Fail (r_in c (a ⋅ b)).
    Fail (r_in a (b)).
    (r_in b (b)).
    Fail (r_in c (b)).
    r_in (ε: Σ) (ε: Σ).
    r_in (ε: Σ) a.
    r_in (ε: Σ) (a ⋅ ε).
    r_in (ε: Σ) (ε ⋅ a).

    (r_contains a (a ⋅ b ⋅ c)).
    (r_contains b (a ⋅ b ⋅ c)).
    (r_contains c (a ⋅ b ⋅ c)).
    (r_contains a (a ⋅ b)).
    (r_contains b (a ⋅ b)).
    Fail (r_contains c (a ⋅ b)).
    Fail (r_contains a (b)).
    (r_contains b (b)).
    Fail (r_contains c (b)).

    (r_contains (a ⋅ b) (a ⋅ b ⋅ c)).
    (r_contains (b ⋅ a) (a ⋅ b ⋅ c)).
    (r_contains (b ⋅ c) (a ⋅ b ⋅ c)).
    (r_contains (c ⋅ a ⋅ b) (a ⋅ b ⋅ c)).
    Fail (r_contains (c ⋅ a ⋅ b) (a ⋅ b)).
    Fail (r_contains (a ⋅ c) (a ⋅ b)).

    r_contains (ε ⋅ (a ⋅ b)) (c ⋅ a ⋅ b).
  Abort.

  Goal forall (a b: Σ) (Pa Pb: iProp), Pa a -> Pb b -> __gwf_mark__ ε (a ⋅ b) -> (Pa ** Pb) (b ⋅ a).
    i. iRefresh.
    iMerge H H0.
    iApply H.
  Qed.


  Goal forall (a b c: Σ) (Pa Pb Pc: iProp), Pa a -> Pb b -> Pc c -> __gwf_mark__ ε (a ⋅ b ⋅ c) -> (Pa ** Pc ** Pb) (c ⋅ b ⋅ a).
    i. iRefresh.
    iSplitR H0.
    - Fail move H0 at top. iSplitL H.
      + Fail move H1 at top. apply H.
      + Fail move H at top. apply H1.
    - Fail move H at top. Fail move H1 at top. apply H0.
  Qed.

  Goal forall P Q, iHyp (P -* Q -* P ** Q) ε.
    i. do 2 iIntro. rewrite URA.unit_idl. (*** TODO: How can we remove this?
I needed to write this because "ss" does not work. create iApply that understands r_clearε? ***)
    iMerge A0 A.
    iDestruct A0.
    (* r in GWF. r in A0. r in A. r. *)
    iMerge A A0.
    ss.
  Qed.

  Goal forall P Q, iHyp (P -* Q -* P ** Q) ε.
    i. do 2 iIntro. rewrite URA.unit_idl.
    iMerge A A0.
    (* r in A. r. r in GWF. *)
    iDestruct A.
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
    iDestruct A0.
    iSplitL A; ss.
  Qed.

End LTEST.

