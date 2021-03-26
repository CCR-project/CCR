(* Control Flag *)
Variant _flag: Set :=
| _break
| _continue
| _fail
.

(* Internals *)
Lemma _equal_f (A B : Type) (f g : A -> B)
      x
      (EQ: f = g)
  :
    f x = g x.
Proof.
  subst. apply eq_refl.
Qed.

Lemma _einit (P Q: Prop)
      (EQ: P = Q)
  :
    Q -> P.
Proof.
  subst. apply id.
Qed.

Ltac _ctx n :=
  match n with
  | O => apply f_equal
  | S ?m => apply _equal_f; _ctx m
  end.

Ltac _prw0 red_tac success :=
  cbn;
  tryif (let f := fresh "f" in
         evar (f:_flag);
         etransitivity;
         [red_tac f|
          match goal with
          | [f0:= ?f1: _flag|- _] =>
            match f1 with
            | _continue => subst f; _prw0 red_tac true
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

Ltac _prw1 k0 k1 X :=
  match X with
  | O => eapply _einit; [(k0; k1)|]
  | S ?n => _prw1 ltac:(k0; _ctx n) k1
  end.

(* Main Tactic *)
Ltac prw red_tac X := _prw1 ltac:(idtac) ltac:(_prw0 red_tac false) X.

Module TUTORIAL.
  Section FOO.
    (* Variables *)
    Variable A B C D: Type.
    Variable a b c d: A.
    Variable x y: B.

    Variable sim: A -> (D * B) * C -> nat -> Prop.

    (* First Step: Prove Reduction Lemmas *)
    Hypothesis foo_red0: a = b.
    Hypothesis foo_red1: b = c.
    Hypothesis foo_red2: c = d.
    Hypothesis foo_red3: x = y.

    (* Second Step: Define Reduction Strategy (= red_tac) *)
    Ltac red_l f := (* f is a flag indicating continue/break/fail. Must set f before return *)
      ((instantiate (f:=_continue); apply foo_red0; fail) ||
       (instantiate (f:=_break); apply foo_red1; fail) ||
       (instantiate (f:=_fail); apply foo_red2; fail)).

    Ltac red_r f :=
      (instantiate (f:=_continue); apply foo_red3; fail).

    (* Done. Let's use it! *)
    Lemma foo: forall (p: C) (q: D) (H: sim c ((q, y), p) 9),
        sim a ((q, x), p) 9.
    Proof.
      intros p q H.
      (* goal = sim a (q, x, p) 9 *)
      prw red_r 2 2 1 0.
      (* prw [red_tac (= red_r)] [l_0 (= 2)] [l_1 (= 2)] [l_2 (= 1)] ... 0 =>
         - find the right l_0th term x0 (= ((q, y), p)) in the goal
         - find the right l_1th term x1 (=      (q, y)) in the   x0
         - find the right l_2th term x2 (=           y) in the   x1
         ...
         - the last argument must be 0. reduce the x2 following _red_r *)
      (* goal = sim a (q, y, p) 9 *)
      prw red_l 3 0.
      (* goal = sim c (q, y, p) 9 *)
      exact H.
    Qed.
  End FOO.
End TUTORIAL.
