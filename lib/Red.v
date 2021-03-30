(* Control Flag *)
Variant _flag: Set :=
| _break
| _continue
| _fail
.

(* Internal *)
Ltac _prw tac success :=
  cbn;
  tryif (let f := fresh "f" in
         evar (f:_flag);
         etransitivity;
         [tac f|
          match goal with
          | [f0:= ?f1: _flag|- _] =>
            match f1 with
            | _continue => subst f; _prw tac true
            | _break => subst f; reflexivity
            | _fail => fail 2
            end
          end])
  then
    idtac
  else
    match success with
    | true => reflexivity
    | false => fail
    end.

(* Main Tactic *)
Ltac prw pat tac :=
  eapply pat; [_prw tac false|].
(* pat: forall _ _ (x0 x1: X), ctx[x0] = ctx[x1] where ctx: X -> Prop*)
(* tac: var -> ltac *)

Module TUTORIAL.
  Section FOO.
    (* Variables *)
    Variable A B: Type.
    Variable a b c d: A.
    Variable x y: B.

    Variable sim: A -> B -> Prop.

    (* First Step: Prove Reduction Lemmas *)
    Hypothesis foo_red0: a = b.
    Hypothesis foo_red1: b = c.
    Hypothesis foo_red2: c = d.
    Hypothesis foo_red3: x = y.

    (* Second Step: Define Reduction Strategy (= tac) *)
    Ltac _red_l f := (* f is a flag indicating continue/break/fail. Must set f before return *)
      ((instantiate (f:=_continue); apply foo_red0; fail) ||
       (instantiate (f:=_break); apply foo_red1; fail) ||
       (instantiate (f:=_fail); apply foo_red2; fail)).

    Ltac _red_r f :=
      (instantiate (f:=_continue); apply foo_red3; fail).

    (* Third Step: Prove Pattern Lemmas (= pat) *)
    Lemma sim_left_pattern p0 p1 q
          (EQ: p0 = p1)
      :
        sim p1 q -> sim p0 q.
    Proof. intros. subst. assumption. Qed.

    Lemma sim_right_pattern p q0 q1
          (EQ: q0 = q1)
      :
        sim p q1 -> sim p q0.
    Proof. intros. subst. assumption. Qed.

    (* Done!! Let' use Generated Reduction Tactics *)
    Ltac red_l := prw sim_left_pattern _red_l. (* prw [pat] [tac] *)
    Ltac red_r := prw sim_right_pattern _red_r.

    Lemma foo (H: sim c y):
      sim a x.
    Proof.
      (* Goal: sim a x *)
      red_l.
      (* Goal: sim c x *)
      red_r.
      (* Goal: sim c y *)
      exact H.
    Qed.
  End FOO.
End TUTORIAL.
