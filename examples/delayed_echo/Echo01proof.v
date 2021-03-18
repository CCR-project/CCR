Require Import Stack1 Client1 Mem1 Mem2.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef Echo0 Echo1 SimModSem.

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
    | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (([(_, (?mr, _))], ?fr), _)  _) ] =>
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
  intros ? wf A; eassert(GWF: ☀) by (split; [refl|exact wf]); clear wf; iRefresh.

Ltac iOwnWf G :=
  match goal with
  | H:iHyp (Own ?r) ?rh |- _ =>
    check_equal H G;
    let name := fresh "WF" in
    (* assert(name: URA.wf r); [eapply wf_downward; [eapply H|eapply wf_downward; et; r_equalize; r_solve]|] *)
    assert(name: URA.wf r); [eapply wf_downward; [eapply H|eapply wf_downward; [|on_gwf ltac:(fun GWF => apply GWF)]; r_equalize; r_solve]|]
  end.





Require Import HTactics.
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















Ltac bring_front H r0 :=
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
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ _  _) ] => idtac
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
  bring_front H r1; bring_front H r0;

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

  Context `{@GRA.inG Mem1.memRA Σ}.
  Lemma unfold_is_list: forall ll xs, is_list ll xs = 
    match xs with
    | [] => ⌜ll = Vnullptr⌝
    | xhd :: xtl =>
      Exists lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (Own (GRA.embed ((lhd,0%Z) |-> [xhd; ltl])))
                                 ** is_list ltl xtl
    end
  .
    { i. destruct xs; ss. }
  Qed.

  Context `{@GRA.inG Echo1.echoRA Σ}.

  Goal forall (a b c d e: Σ) (GWF: __gwf_mark__ ε (d ⋅ c)), iHyp ⌜True⌝ (d ⋅ c) -> iHyp ⌜True⌝ (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)).
    i. bar. bring_front H1 d. bring_front H1 c.
    match goal with | |- ?G => match G with | iHyp _ (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
  Abort.

  Goal forall (a b c d e f: Σ) (GWF: __gwf_mark__ (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)) (a ⋅ (b ⋅ c) ⋅ (d ⋅ e))), iHyp ⌜True⌝ ((a ⋅ d) ⋅ (c ⋅ b)) -> iHyp ⌜True⌝ (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)).
    i. bar. bring_front H1 d. bring_front H1 c.
    match goal with | |- ?G => match G with | iHyp _ (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
    match goal with | [H: __gwf_mark__ ?rs0 ?rs1 |- _ ] => match rs0 with | (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)) => idtac | _ => fail end end.
    match goal with | [H: __gwf_mark__ ?rs0 ?rs1 |- _ ] => match rs1 with | (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
    match type of H1 with | iHyp _ ?rs => match rs with | (c ⋅ d ⋅ a ⋅ b) => idtac | _ => fail end end.
  Abort.

  Goal forall (a b c d e f: Σ) (GWF: __gwf_mark__ ε (a ⋅ (b ⋅ c) ⋅ (d ⋅ e))), iHyp ⌜True⌝ ((a ⋅ d) ⋅ (c ⋅ b)) -> iHyp ⌜True⌝ (a ⋅ (b ⋅ c) ⋅ (d ⋅ e)).
    i. bar. bring_front H1 d. bring_front H1 c.
    match goal with | |- ?G => match G with | iHyp _ (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
    match goal with | [H: __gwf_mark__ ?rs0 ?rs1 |- _ ] => match rs0 with | ε => idtac | _ => fail end end.
    match goal with | [H: __gwf_mark__ ?rs0 ?rs1 |- _ ] => match rs1 with | (c ⋅ d ⋅ a ⋅ b ⋅ e) => idtac | _ => fail end end.
    match type of H1 with | iHyp _ ?rs => match rs with | (c ⋅ d ⋅ a ⋅ b) => idtac | _ => fail end end.
  Abort.

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

  (* Lemma echo_ra_merge2 *)
  (*       ll0 ns0 ll1 ns1 *)
  (*   : *)
  (*     iHyp (Own (GRA.embed (echo_black ll0 ns0)) -* Own (GRA.embed (echo_white ll1 ns1)) *)
  (*               -* (⌜ll1 = ll0 /\ ns1 = ns0⌝ ** Own (GRA.embed (echo_black ll0 ns0)) ** Own (GRA.embed (echo_white ll1 ns1)))) ε *)
  (* . *)
  (* Proof. *)
  (*   iIntro. iIntro. *)
  (*   { *)
  (*     iMerge A A0. rewrite <- own_sep in A. rewrite GRA.embed_add in A. *)
  (*     iOwnWf A. eapply GRA.embed_wf in WF. des. eapply URA.auth_included in WF. des. *)
  (*     Local Transparent URA.add. *)
  (*     rr in WF. des. cbn in WF. *)
  (*     Local Opaque URA.add. *)
  (*     des_ifs. *)
  (*     rewrite <- GRA.embed_add in A. rewrite own_sep in A. iDestruct' A. *)
  (*     iSplitL A; ss. *)
  (*     - iSplitP; ss. *)
  (*   } *)
  (* Qed. *)
  Definition purify (P: iProp): Prop := ⌜True⌝ ⊢ P.
  (* Definition purify (P: iProp): Prop := P ε. *)
  (* Definition purify (P: iProp): Prop := forall r, P r. *)
  (* Coercion unpure_coercion (P: iProp): Prop := unpure P. *)
  (* Coercion unpure_coercion := unpure. *)

  Lemma echo_ra_merge
        ll0 ns0 ll1 ns1
    :
      (* iHyp (Own (GRA.embed (echo_black ll0 ns0)) -* Own (GRA.embed (echo_white ll1 ns1)) -* (⌜ll1 = ll0 /\ ns1 = ns0⌝)) ε *)
      purify (Own (GRA.embed (echo_black ll0 ns0)) -* Own (GRA.embed (echo_white ll1 ns1)) -* (⌜ll1 = ll0 /\ ns1 = ns0⌝))
  .
  Proof.
    iIntro; clear A.
    do 2 iIntro.
    {
      iMerge A A0. rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. eapply GRA.embed_wf in WF. des. eapply URA.auth_included in WF. des.
      Local Transparent URA.add.
      rr in WF. des. cbn in WF.
      Local Opaque URA.add.
      des_ifs.
    }
  Qed.

  Lemma echo_ra_white
        ll0 ns0 ll1 ns1
    :
      (* iHyp (Own (GRA.embed (echo_white ll0 ns0)) -* Own (GRA.embed (echo_white ll1 ns1)) -* ⌜False⌝) ε *)
      purify (Own (GRA.embed (echo_white ll0 ns0)) -* Own (GRA.embed (echo_white ll1 ns1)) -* ⌜False⌝)
  .
  Proof.
    iIntro; clear A.
    do 2 iIntro.
    {
      exfalso. iMerge A A0.
      rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. clear - WF. apply GRA.embed_wf in WF. des. ss.
    }
  Qed.

  Lemma echo_ra_black
        ll0 ns0 ll1 ns1
    :
      (* iHyp (Own (GRA.embed (echo_black ll0 ns0)) -* Own (GRA.embed (echo_black ll1 ns1)) -* ⌜False⌝) ε *)
      purify (Own (GRA.embed (echo_black ll0 ns0)) -* Own (GRA.embed (echo_black ll1 ns1)) -* ⌜False⌝)
  .
  Proof.
    iIntro; clear A.
    do 2 iIntro.
    {
      exfalso. iMerge A A0.
      rewrite <- own_sep in A. rewrite GRA.embed_add in A.
      iOwnWf A. clear - WF. apply GRA.embed_wf in WF. des. ss.
    }
  Qed.
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
Ltac r_until_bar := until_bar ltac:(fun H => r in H).

Notation "'⌞' P '⌟'" := (purify P).
Ltac iPurify H := let name := fresh "my_r" in
                  specialize (H ε URA.wf_unit I); rewrite intro_iHyp in H;
                  on_gwf ltac:(fun GWF => rewrite <- URA.unit_id in GWF; set (name:=ε) in GWF, H; clearbody name).
Ltac iMod H :=
  match type of H with
  | purify _ => iPurify H
  | iHyp (⌜ _ ⌝) _ => iPure H
  | iHyp ( |=> _ ) _ => iUpdate H
  | _ => fail
  end
.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.
  Context `{@GRA.inG Echo1.echoRA Σ}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  Eval compute in (@URA.car Mem1._memRA).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ) (ll: val),
        (<<SRC: mrps_src0 = Maps.add "Echo" (mr, tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "Echo" (ε, ll↑) Maps.empty>>) /\
        (* (<<SIM: (iHyp (⌜ll = Vnullptr⌝ ∨ (Exists ns, (Own(GRA.embed(echo_black ns))) ** is_list ll (List.map Vint ns))) mr)>>) *)
        (* (<<SIM: (iHyp (Exists ns, (Own(GRA.embed(echo_black ns))) *)
        (*                             ** (is_list ll (List.map Vint ns) ∨ (Own(GRA.embed(echo_white ns))))) mr)>>) *)
        (<<SIM: (iHyp (Exists ns, ((Own(GRA.embed(echo_black ll ns))) ** is_list ll (List.map Vint ns)) ∨ (Own(GRA.embed(echo_white ll ns)))) mr)>>)
  .

  Local Opaque is_list.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.
  Opaque points_to.

  Lemma gwf_update_cur: forall past cur0 cur1, cur0 = cur1 -> __gwf_mark__ past cur0 -> __gwf_mark__ past cur1. i. subst. eauto. Qed.
  Lemma gwf_dummy: (__gwf_mark__ ε ε). Proof. split; try refl. apply URA.wf_unit. Qed.

  Theorem correct: ModSemPair.sim Echo1.EchoSem Echo0.EchoSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. unfold alist_add; cbn. esplits; ss; eauto. hexploit gwf_dummy; i. eexists nil; ss; iRefresh.
      rewrite unfold_is_list. left; iRefresh. iSplitP; ss. eexists ε. rewrite URA.unit_id; ss.
    }

    Opaque URA.add.
    econs; ss.
    { unfold echoF, echo_body. init.
      harg_tac. des_ifs_safe. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      iRefresh. do 2 iDestruct PRE. iMod A. iMod A0. clarify.
      iDestruct SIM.
      destruct SIM as [A|A]; iRefresh; cycle 1.
      { hexploit echo_ra_white; et. intro T. iMod T. iSpecialize T A. iSpecialize T PRE. iMod T; des; ss. }

      iDestruct A. subst.
      rename x into ns. rename x0 into ns0.
      assert(l = ns /\ v = ll); des; subst.
      { hexploit echo_ra_merge; et. intro T. iPurify T. iSpecialize T A. iSpecialize T PRE. iMod T; des; ss. }




      steps. unfold hcall, ccall. steps.
      unfold body_to_tgt. unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.

      hcall_tac __ __ (A, A0) PRE (@URA.unit Σ); ss; et.
      { esplits; ss; et. eexists; iRefresh. left; iRefresh. iSplitL A; ss.
        - iApply A; ss.
        - iApply A0; ss.
      }
      des; subst. rewrite Any.upcast_downcast. steps. rewrite Any.upcast_downcast. steps.



      iDestruct SIM. destruct SIM as [SIM|SIM]; iRefresh; cycle 1.
      { hexploit echo_ra_white; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T PRE. iMod T; des; ss. }
      iDestruct SIM. subst.
      assert(ll0 = ll /\ x = ns); des; subst.
      { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T PRE. iMod T; des; ss. }
      subst.




      destruct (unint vret_src) eqn:T; cycle 1.
      { steps. unfold triggerUB. steps. }
      destruct vret_src; ss. clarify. steps.

      destruct (dec z (- 1)%Z).
      - subst. ss. steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ __ (A, SIM) (@URA.unit Σ) PRE; ss; et.
        { instantiate (2:= (_, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss; et. }
        { esplits; ss; et. }
        { esplits; ss; et. exists ns; iRefresh. left; iRefresh. iSplit SIM A; ss. r_solve. }
        steps.
        hret_tac mr (@URA.unit Σ); ss.
        { eapply URA.extends_updatable. esplit. r_equalize; r_solve. }
        { iRefresh. iDestruct SIM0. esplits; eauto. eexists; iRefresh. eauto. }
      - steps.
        force_l. eexists 1. steps. rewrite Any.upcast_downcast. ss. steps.

        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("push", [ll; Vint z]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ (ord_pure 2) PRE SIM A; ss; et.
        { instantiate (1:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply A; ss. }
        { esplits; ss; et. exists ns; iRefresh. right; iRefresh; ss. }
        des; iRefresh. do 2 iDestruct POST0. iMod A. subst. apply Any.upcast_inj in A. des; clarify.
        iDestruct SIM0. destruct SIM0; iRefresh.
        { iDestruct' H1. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T H1. iMod T; des; ss. }

        rename H1 into A.
        assert(ll0 = ll /\ x8 = ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T A. iMod T; des; ss. }




        iMerge A SIM. rewrite <- own_sep in A. rewrite GRA.embed_add in A. rewrite URA.add_comm in A.
        eapply own_upd in A; cycle 1; [|rewrite intro_iHyp in A;iMod A].
        { eapply GRA.embed_updatable. instantiate (1:= echo_black x (z :: ns) ⋅ echo_white x (z :: ns)).
          eapply URA.auth_update. rr. ii. des; ss. destruct ctx; ss; clarify.
        }
        rewrite <- GRA.embed_add in A. rewrite own_sep in A. iDestruct A. subst.



        rewrite unfold_APC. steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast in *. steps.

        hcall_tac __ ord_top (POST0, A) (@URA.unit Σ) A0; ss; et.
        { instantiate (1:=(_, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss; et. }
        { esplits; ss; eauto. exists (z :: ns); iRefresh. left; iRefresh. iSplit A POST0; ss; r_solve. }
        steps.
        hret_tac mr0 (@URA.unit Σ); ss.
        { eapply URA.extends_updatable; et. r_equalize; r_solve. }
        { esplits; eauto. }
    }
    econs; ss.
    { unfold echo_finishF, echo_finish_body. init. harg_tac; des_ifs_safe; iRefresh. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      do 2 iDestruct PRE. iMod A. iMod A0. clarify.
      iDestruct SIM.
      destruct SIM as [A|A]; iRefresh; cycle 1.
      { hexploit echo_ra_white; et. intro T. iMod T. iSpecialize T A. iSpecialize T PRE. iMod T; des; ss. }

      iDestruct A. subst.
      rename x into ns. rename x0 into ns0.
      assert(v = ll /\ l = ns).
      { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T PRE. iMod T; des; ss. }
      des; subst.




      steps. unfold hcall, ccall. rewrite unfold_is_list in A0. destruct ns; ss; steps.
      - unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
        rewrite Any.upcast_downcast. steps. iMod A0. subst.
        hret_tac x3 (@URA.unit Σ); ss. (********************* TODO **************************************)
        { eapply URA.extends_updatable. esplit. r_equalize; r_solve. }
        { iRefresh. esplits; ss; eauto. exists nil; iRefresh. left; iRefresh. iSplitL A; ss. } (************ TODO ************)
      - rewrite Any.upcast_downcast. steps. do 4 iDestruct A0. iMod A0. subst. ss.
        unfold interp_hCallE_tgt, APC. steps. force_l. exists 3. steps.

        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("alloc", [Vint 1]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ (ord_pure 1) PRE (A, A1, A2) (@URA.unit Σ); ss; et.
        { esplits; try refl; iRefresh. instantiate (1:=1). esplits; ss; et. }
        { esplits; ss; et. eexists; iRefresh. right; iRefresh; ss; et. }
        des; iRefresh. do 2 iDestruct POST. iMod POST. subst.
        apply_all_once Any.upcast_inj. des; clarify. steps. rewrite Any.upcast_downcast in *. clarify.
        iDestruct SIM. destruct SIM as [SIM|SIM]; iRefresh.
        { iDestruct' SIM. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }
        assert(ll = (Vptr x 0) /\ x10 = z :: ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }




        rename x into hd. rename x4 into tmp.
        iMerge A1 A2.
        iAssert A1 (is_list (Vptr hd 0) (List.map Vint (z :: ns))).
        { iIntro. rewrite unfold_is_list. cbn.
          iDestruct' A2. do 2 eexists; iRefresh.
          iSplitL A.
          { iSplitP; ss; et. }
          { iRefresh; ss. }
        }




        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("pop2", [Vptr hd 0; Vptr tmp 0]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ (ord_pure 2) SIM A (A0, A2); ss; et.
        { instantiate (1:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss.
          iSplitR (A0); ss; et.
          - iSplitP; ss. eauto.
          - eexists; iRefresh. eauto.
        }
        { esplits; ss; et. eexists; iRefresh. right; iRefresh; ss; et. }
        des; iRefresh. iDestruct SIM0. do 3 iDestruct POST. iMod POST. subst.
        apply_all_once Any.upcast_inj. des; clarify. steps.
        rewrite Any.upcast_downcast in *. clarify.
        rename SIM0 into SIM. destruct SIM as [SIM|SIM]; iRefresh.
        { iDestruct' SIM. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }
        assert(ll = Vptr hd 0 /\ x = z :: ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }



        iMerge A SIM. rewrite <- own_sep in A. rewrite GRA.embed_add in A.
        eapply own_upd in A; cycle 1; [|rewrite intro_iHyp in A;iMod A].
        { eapply GRA.embed_updatable. instantiate (1:= echo_black v (ns) ⋅ echo_white v (ns)).
          eapply URA.auth_update. rr. ii. des; ss. destruct ctx; ss; clarify.
        }
        rewrite <- GRA.embed_add in A. rewrite own_sep in A. iDestruct A.



        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("load", [Vptr tmp 0]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ (ord_pure 1) A2 (A, A1) A0; ss; et.
        { instantiate (1:=(_, _, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. eauto. }
        { esplits; ss; et. eexists; iRefresh. right; iRefresh; ss; et. }
        des; iRefresh. iDestruct SIM. iDestruct POST. iMod A0. subst.
        apply_all_once Any.upcast_inj. des; clarify. steps.
        rewrite Any.upcast_downcast in *. clarify.
        destruct SIM as [SIM|SIM]; iRefresh.
        { iDestruct' SIM. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }
        assert(v = ll /\ x = ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }





        rewrite unfold_APC. steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ (ord_top) SIM (A, A1, POST) (@URA.unit Σ); ss; et.
        { esplits; ss; et. eexists; iRefresh. right; iRefresh; ss; et. }
        des; iRefresh. subst. iDestruct SIM0.
        rename SIM0 into SIM. destruct SIM as [SIM|SIM]; iRefresh.
        { iDestruct' SIM. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }
        assert(ll0 = ll /\ x = ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T A. iSpecialize T SIM. iMod T; des; ss. }



        steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast in *. steps.
        hcall_tac __ (ord_top) (A, A1) POST SIM; ss; et.
        { instantiate (1:= (_, _)). cbn. iRefresh. iSplitP; ss. iSplitP; ss; et. }
        { esplits; ss; et. eexists; iRefresh. left; iRefresh. iSplitL A; ss; et. }
        des; iRefresh. subst. iDestruct SIM0.

        steps.
        hret_tac mr3 (@URA.unit Σ); ss.
        { eapply URA.extends_updatable. r_equalize; r_solve. }
        { iRefresh. esplits; eauto. eexists; iRefresh. eauto. }
    }
  Unshelve.
    all: ss.
    all: try (by repeat econs; et).
  Qed.

End SIMMODSEM.


