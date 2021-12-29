Require Import Red.
Require Import Coqlib.
Require Import ITreelib.
Require Import ModSemE.
Require Import Any.

Local Open Scope nat_scope.

Set Implicit Arguments.



Ltac get_head term :=
  match term with
  | ?f ?x => get_head f
  | _ => term
  end
.

Ltac get_head2 term :=
  lazymatch term with
  | ?f ?x =>
    let ty := type of x in
    lazymatch ty with
    | context[ReSum] => term
    | _ => get_head2 f
    end
  | _ => term
  end
.

(* Ltac iSolveTC := *)
(*   solve [once (typeclasses eauto)]. *)

(* Ltac get_tail term := *)
(*   match term with *)
(*   | ?f ?x => x *)
(*   end *)
(* . *)

Ltac get_itr term :=
  (* repeat multimatch term with *)
  (*        | _ ?x => match type of x with itree _ _ => x end *)
  (*        | _ ?x _ => match type of x with itree _ _ => x end *)
  (*        | _ ?x _ _ => match type of x with itree _ _ => x end *)
  (*        | _ ?x _ _ _ => match type of x with itree _ _ => x end *)
  (*        | _ ?x _ _ _ _ => match type of x with itree _ _ => x end *)
  (*        | _ ?x _ _ _ _ _ => match type of x with itree _ _ => x end *)
  (*        end *)
  (* repeat multimatch term with *)
  (*        | _ ?x => match type of x with itree _ _ => constr:(x) end *)
  (*        | _ ?x _ => match type of x with itree _ _ => constr:(x) end *)
  (*        | _ ?x _ _ => match type of x with itree _ _ => constr:(x) end *)
  (*        | _ ?x _ _ _ => match type of x with itree _ _ => constr:(x) end *)
  (*        | _ ?x _ _ _ _ => match type of x with itree _ _ => constr:(x) end *)
  (*        | _ ?x _ _ _ _ _ => match type of x with itree _ _ => constr:(x) end *)
  (*        end *)
  match term with
  | _ ?x => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ _ => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ _ _ => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ _ _ _ => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ _ _ _ _ => match type of x with itree _ _ => constr:(x) end
  end
.

Ltac get_nth term n :=
  match term with
  | ?f ?x =>
    match n with
    | O => x
    | S ?m => get_nth f m
      (* let res := get_nth x m in *)
      (* constr:(res) *)
    end
  | ?x =>
    match n with
    | O => x
    end
  end
.

Goal forall (f: nat -> nat -> nat -> nat -> nat) a b c d, f a b c d = 0.
  i.
  let tmp := get_nth (f a b c d) 0 in pose tmp as d'. assert(d' = d) by refl.
  let tmp := get_nth (f a b c d) 1 in pose tmp as c'. assert(c' = c) by refl.
  let tmp := get_nth (f a b c d) 2 in pose tmp as b'. assert(b' = b) by refl.
  let tmp := get_nth (f a b c d) 3 in pose tmp as a'. assert(a' = a) by refl.
  let tmp := get_nth (f a b c d) 4 in pose tmp as f'. assert(f' = f) by refl.
Abort.



(*** TODO: move to better place or use dedicated name (like ired_box) ***)
Variant Box: Type :=
| mk_box: forall (A:Type), A -> Box
.

Class red_database (interp: Box) := mk_rdb {
  rdb_pos: nat;
  rdb_bind: Box;
  rdb_tau: Box;
  rdb_ret: Box;
  rdb_trigger0: Box;
  rdb_trigger1: Box;
  rdb_trigger2: Box;
  rdb_trigger3: Box;
  rdb_UB: Box;
  rdb_NB: Box;
  rdb_unwrapU: Box;
  rdb_unwrapN: Box;
  rdb_assume: Box;
  rdb_guarantee: Box;
  rdb_ext: Box;
}
.
Arguments mk_rdb [interp].
Arguments rdb_pos [interp].
Arguments rdb_bind [interp].
Arguments rdb_tau [interp].
Arguments rdb_ret [interp].
Arguments rdb_trigger0 [interp].
Arguments rdb_trigger1 [interp].
Arguments rdb_trigger2 [interp].
Arguments rdb_trigger3 [interp].
Arguments rdb_UB [interp].
Arguments rdb_NB [interp].
Arguments rdb_unwrapU [interp].
Arguments rdb_unwrapN [interp].
Arguments rdb_assume [interp].
Arguments rdb_guarantee [interp].
Arguments rdb_ext [interp].






(*** TODO: move to ITreeLib ***)
(*** TODO: remove redundancy with HoareDef - bind_eta ***)
Lemma bind_ext E X Y itr0 itr1 (ktr: ktree E X Y): itr0 = itr1 -> itr0 >>= ktr = itr1 >>= ktr. i; subst; refl. Qed.

Lemma bind_extk: forall [E : Type -> Type] [X Y : Type] [itr: itree E X] (ktr0 ktr1: ktree E X Y),
    (forall x, ktr0 x = ktr1 x) -> (itr >>= ktr0) = (itr >>= ktr1)
.
Proof. i. f_equiv. eapply func_ext. et. Qed.

Lemma tau_ext: forall [E : Type -> Type] [X : Type] [itr0 itr1: itree E X],
    itr0 = itr1 -> (tau;; itr0) = (tau;; itr1)
.
Proof. i. grind. Qed.


(* Tactic Notation "debug" string(str) := idtac str. (*** debug mode ***) *)
(* Tactic Notation "debug" string(str) := idtac. (*** release mode ***) *)

Ltac _red_itree f :=
  lazymatch goal with
  | [ |- ?itr >>= ?ktr = _] =>
    lazymatch itr with
    | _ >>= _ =>
      instantiate (f:=_continue); apply bind_bind; fail
    | Tau _ =>
      instantiate (f:=_break); apply bind_tau; fail
    | Ret _ =>
      instantiate (f:=_continue); apply bind_ret_l; fail
    (* | _ => *)
    (*   eapply bind_extk; i; *)
    (*   _red_itree f *)
    end
  | [ |- trigger _ = _] =>
    instantiate (f:=_break); apply bind_ret_r_rev; fail
  (* | [ |- (tau;; _) = _ ] => *)
  (*   eapply tau_ext; _red_itree f *)
  | _ => fail
  end.

Ltac __red_interp f term :=
  match term with
  | unwrapU (@Any.downcast ?A (@Any.upcast ?A ?a)) =>
    instantiate (f:=_continue); apply f_equal; apply Any.upcast_downcast; fail
  | unwrapU (Any.split (Any.pair ?a0 ?a1)) =>
    instantiate (f:=_continue); apply f_equal; apply Any.pair_split; fail
  | unwrapN (@Any.downcast ?A (@Any.upcast ?A ?a)) =>
    instantiate (f:=_continue); apply f_equal; apply Any.upcast_downcast; fail
  | unwrapN (Any.split (Any.pair ?a0 ?a1)) =>
    instantiate (f:=_continue); apply f_equal; apply Any.pair_split; fail
  | _ =>

  (* idtac "__red_interp"; *)
  (* idtac term; *)
  let my_interp := get_head2 term in
  (* idtac itr; *)
  let tc := fresh "_TC_" in
  unshelve evar (tc: @red_database (mk_box (my_interp))); [typeclasses eauto|];
  let name := fresh "TMP" in
  let _nth := constr:(rdb_pos tc) in
  let nth := (eval simpl in _nth) in
  let itr := get_nth term nth in
  lazymatch itr with
  | ?i0 >>= ?k0 =>
    (* idtac "bind"; *)
    instantiate (f:=_continue); pose (rdb_bind tc) as name; cbn in name;
    (*** Note: Why not just "apply lemma"? Because of Coq bug. (Anomaly) ***)
    match goal with | name := mk_box ?lemma |- _ => first[apply (@lemma _ _ i0 k0)|apply lemma] end
  | Tau _ =>
    instantiate (f:=_continue); pose (rdb_tau tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | Ret _ =>
    (* idtac "ret"; *)
    instantiate (f:=_continue); pose (rdb_ret tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | trigger ?e =>
    instantiate (f:=_continue);
    ((pose (rdb_trigger0 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger1 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger2 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger3 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     fail 3
    )
  | triggerUB =>
    instantiate (f:=_continue); pose (rdb_UB tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | triggerNB =>
    instantiate (f:=_continue); pose (rdb_NB tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | unwrapU _ =>
    instantiate (f:=_continue); pose (rdb_unwrapU tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | unwrapN _ =>
    instantiate (f:=_continue); pose (rdb_unwrapN tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | assume _ =>
    instantiate (f:=_continue); pose (rdb_assume tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | guarantee _ =>
    instantiate (f:=_continue); pose (rdb_guarantee tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | ?term =>
    (* idtac "term"; *)
    pose (rdb_ext tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma end;
    subst tc;
    __red_interp f term
  end
end
.

Ltac _red_interp f :=
  (* idtac "_red_interp"; *)
  lazymatch goal with
  | [ |- ?term >>= _ = _ ] =>
    (* idtac "_red_interp_bind"; *)
    apply bind_ext; __red_interp f term
  | [ |- ?term = _] =>
    (* idtac "_red_interp_term"; *)
    __red_interp f term
  end
.

Ltac _red_gen f :=
  (* idtac "DEBUG:_red_gen"; *)
  _red_interp f || _red_itree f || fail.





Lemma resum_itr_bind
      E (R S: Type)
      (s: itree E R) (k : R -> itree E S)
      `{E -< F}
  :
    (resum_itr (s >>= k))
    =
    ((resum_itr (E:=E) (F:=F) s) >>= (fun r => resum_itr (k r))).
Proof.
  unfold resum_itr in *. grind.
Qed.

Section RESUM.

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  (* Context {E F: Type -> Type}. *)
  (* Context `{eventE -< E}. *)
  (* Context `{E -< F}. *)
  Context `{PRF: E -< F}.
  Context `{eventE -< E}.
  Let eventE_F: eventE -< F. rr. ii. eapply PRF. eapply H. eapply X. Defined.
  Local Existing Instance eventE_F.

  (* Lemma resum_itr_bind *)
  (*       (R S: Type) *)
  (*       (s: itree _ R) (k : R -> itree _ S) *)
  (*   : *)
  (*     (resum_itr (s >>= k)) *)
  (*     = *)
  (*     ((resum_itr (E:=E) (F:=F) s) >>= (fun r => resum_itr (k r))). *)
  (* Proof. *)
  (*   unfold resum_itr in *. grind. *)
  (* Qed. *)

  Lemma resum_itr_tau
        (U: Type)
        (t : itree _ U)
    :
      (resum_itr (E:=E) (F:=F) (Tau t))
      =
      (Tau (resum_itr t)).
  Proof.
    unfold resum_itr in *. grind.
  Qed.

  Lemma resum_itr_ret
        (U: Type)
        (t: U)
    :
      ((resum_itr (E:=E) (F:=F) (Ret t)))
      =
      Ret t.
  Proof.
    unfold resum_itr in *. grind.
  Qed.

  Lemma resum_itr_event
        (R: Type)
        (i: E R)
    :
      (resum_itr (E:=E) (F:=F) (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold resum_itr in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma resum_itr_triggerUB
        (R: Type)
    :
      (resum_itr (E:=E) (F:=F) (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold resum_itr, triggerUB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma resum_itr_triggerNB
        (R: Type)
    :
      (resum_itr (E:=E) (F:=F) (triggerNB))
      =
      triggerNB (A:=R).
  Proof.
    unfold resum_itr, triggerNB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma resum_itr_unwrapU
        (R: Type)
        (i: option R)
    :
      (resum_itr (E:=E) (F:=F) (unwrapU i))
      =
      (unwrapU i).
  Proof.
    unfold resum_itr. unfold unwrapU. des_ifs; grind. eapply resum_itr_triggerUB.
  Qed.

  Lemma resum_itr_unwrapN
        (R: Type)
        (i: option R)
    :
      (resum_itr (E:=E) (F:=F) (unwrapN i))
      =
      (unwrapN i).
  Proof.
    unfold resum_itr. unfold unwrapN. des_ifs; grind. eapply resum_itr_triggerNB.
  Qed.

  Lemma resum_itr_assume
        P
    :
      (resum_itr (E:=E) (F:=F) (assume P))
      =
      (assume P;;; tau;; Ret tt)
  .
  Proof.
    unfold resum_itr, assume. grind. rewrite unfold_interp; cbn. grind.
  Qed.

  Lemma resum_itr_guarantee
        P
    :
      (resum_itr (E:=E) (F:=F) (guarantee P))
      =
      (guarantee P;;; tau;; Ret tt).
  Proof.
    unfold resum_itr, guarantee. grind. rewrite unfold_interp; cbn. grind.
  Qed.

  Lemma resum_itr_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (resum_itr (E:=E) (F:=F) itr0)
      =
      (resum_itr itr1)
  .
  Proof. subst; et. Qed.

  Global Program Instance resum_itr_rdb: red_database (mk_box (@resum_itr E F PRF)) :=
    mk_rdb
      0
      (mk_box resum_itr_bind)
      (mk_box resum_itr_tau)
      (mk_box resum_itr_ret)
      (mk_box resum_itr_event)
      (mk_box True)
      (mk_box True)
      (mk_box True)
      (mk_box resum_itr_triggerUB)
      (mk_box resum_itr_triggerNB)
      (mk_box resum_itr_unwrapU)
      (mk_box resum_itr_unwrapN)
      (mk_box resum_itr_assume)
      (mk_box resum_itr_guarantee)
      (mk_box resum_itr_ext)
  .

  Global Opaque resum_itr.

End RESUM.



Module TEST.
Section TEST.

  Ltac my_red_both := try (prw _red_gen 2 0); try (prw _red_gen 1 0).

  Local Set Typeclasses Depth 50.

  Goal forall (itr: itree (void1 +' void1 +' eventE) nat), resum_itr (tau;; itr) = tau;; resum_itr itr.
  Proof. i. Timeout 1 my_red_both. refl. Qed.

  Goal forall (itr: itree (void1 +' eventE) nat), resum_itr (F:= void1 +' eventE +' void1) (tau;; itr) = tau;; resum_itr itr.
  Proof. i. Timeout 1 my_red_both. refl. Qed.

  Goal forall (itr: itree (void1 +' eventE) nat) (ktr: ktree _ nat nat),
      resum_itr (F:= void1 +' eventE +' void1) (itr >>= ktr) = resum_itr itr >>= (fun r => resum_itr (ktr r)).
  Proof. i. Timeout 1 my_red_both. refl. Qed.

  Local Unset Typeclasses Depth.
  (* Print Options. *)

  Variable E F G H: Type -> Type.
  Variable x: itree (eventE +' E) ~> itree (eventE +' F).
  Variable y: itree (eventE +' F) ~> itree (eventE +' G).
  Variable z: itree (eventE +' G) ~> itree (eventE +' H).



  Hypothesis x_bind: forall R S itr (ktr: ktree _ R S), (x (itr >>= ktr)) = (r <- x itr;; x (ktr r)).
  Hypothesis x_tau: forall R (i: itree _ R), (x (tau;; i)) = tau;; (x i).
  Hypothesis x_ret: forall R (i: R), (x (Ret i)) = Ret i.
  Hypothesis x_triggere: forall R (i: eventE R), (x (trigger i)) = (trigger i >>= (fun r => tau;; Ret r)).
  Hypothesis x_UB: forall R, (x triggerUB) = (triggerUB: itree _ R).
  Hypothesis x_NB: forall R, (x triggerNB) = (triggerNB: itree _ R).
  Hypothesis x_unwrapU: forall R (i: option R), (x (unwrapU i)) = (unwrapU i).
  Hypothesis x_unwrapN: forall R (i: option R), (x (unwrapN i)) = (unwrapN i).
  Hypothesis x_assume: forall P, (x (assume P)) = assume P >>= (fun _ => tau;; Ret tt).
  Hypothesis x_guarantee: forall P, (x (guarantee P)) = guarantee P >>= (fun _ => tau;; Ret tt).
  Hypothesis x_ext: forall R (i0 i1: itree _ R), i0 = i1 -> (x i0) = (x i1).

  Global Program Instance x_rdb: red_database (mk_box x) :=
    mk_rdb
      0
      (mk_box (x_bind))
      (mk_box (x_tau))
      (mk_box (x_ret))
      (mk_box (x_triggere))
      (mk_box (x_triggere))
      (mk_box (x_triggere))
      (mk_box (x_triggere))
      (mk_box (x_UB))
      (mk_box (x_NB))
      (mk_box (x_unwrapU))
      (mk_box (x_unwrapN))
      (mk_box (x_assume))
      (mk_box (x_guarantee))
      (mk_box (x_ext))
  .

  Hypothesis y_bind: forall R S itr (ktr: ktree _ R S), (y (itr >>= ktr)) = (r <- y itr;; y (ktr r)).
  Hypothesis y_tau: forall R (i: itree _ R), (y (tau;; i)) = tau;; (y i).
  Hypothesis y_ret: forall R (i: R), (y (Ret i)) = Ret i.
  Hypothesis y_triggere: forall R (i: eventE R), (y (trigger i)) = (trigger i >>= (fun r => tau;; Ret r)).
  Hypothesis y_UB: forall R, (y triggerUB) = (triggerUB: itree _ R).
  Hypothesis y_NB: forall R, (y triggerNB) = (triggerNB: itree _ R).
  Hypothesis y_unwrapU: forall R (i: option R), (y (unwrapU i)) = (unwrapU i).
  Hypothesis y_unwrapN: forall R (i: option R), (y (unwrapN i)) = (unwrapN i).
  Hypothesis y_assume: forall P, (y (assume P)) = assume P >>= (fun _ => tau;; Ret tt).
  Hypothesis y_guarantee: forall P, (y (guarantee P)) = guarantee P >>= (fun _ => tau;; Ret tt).
  Hypothesis y_ext: forall R (i0 i1: itree _ R), i0 = i1 -> (y i0) = (y i1).

  Global Program Instance y_rdb: red_database (mk_box y) :=
    mk_rdb
      0
      (mk_box (y_bind))
      (mk_box (y_tau))
      (mk_box (y_ret))
      (mk_box (y_triggere))
      (mk_box (y_triggere))
      (mk_box (y_triggere))
      (mk_box (y_triggere))
      (mk_box (y_UB))
      (mk_box (y_NB))
      (mk_box (y_unwrapU))
      (mk_box (y_unwrapN))
      (mk_box (y_assume))
      (mk_box (y_guarantee))
      (mk_box (y_ext))
  .

  Hypothesis z_bind: forall R S itr (ktr: ktree _ R S), (z (itr >>= ktr)) = (r <- z itr;; z (ktr r)).
  Hypothesis z_tau: forall R (i: itree _ R), (z (tau;; i)) = tau;; (z i).
  Hypothesis z_ret: forall R (i: R), (z (Ret i)) = Ret i.
  Hypothesis z_triggere: forall R (i: eventE R), (z (trigger i)) = (trigger i >>= (fun r => tau;; Ret r)).
  Hypothesis z_UB: forall R, (z triggerUB) = (triggerUB: itree _ R).
  Hypothesis z_NB: forall R, (z triggerNB) = (triggerNB: itree _ R).
  Hypothesis z_unwrapU: forall R (i: option R), (z (unwrapU i)) = (unwrapU i).
  Hypothesis z_unwrapN: forall R (i: option R), (z (unwrapN i)) = (unwrapN i).
  Hypothesis z_assume: forall P, (z (assume P)) = assume P >>= (fun _ => tau;; Ret tt).
  Hypothesis z_guarantee: forall P, (z (guarantee P)) = guarantee P >>= (fun _ => tau;; Ret tt).
  Hypothesis z_ext: forall R (i0 i1: itree _ R), i0 = i1 -> (z i0) = (z i1).

  Global Program Instance z_rdb: red_database (mk_box z) :=
    mk_rdb
      0
      (mk_box (z_bind))
      (mk_box (z_tau))
      (mk_box (z_ret))
      (mk_box (z_triggere))
      (mk_box (z_triggere))
      (mk_box (z_triggere))
      (mk_box (z_triggere))
      (mk_box (z_UB))
      (mk_box (z_NB))
      (mk_box (z_unwrapU))
      (mk_box (z_unwrapN))
      (mk_box (z_assume))
      (mk_box (z_guarantee))
      (mk_box (z_ext))
  .

  Goal forall T U V (i: itree _ T) (j: ktree _ T U) (k: ktree _ U V),
      x (i >>= j >>= k) = iret <- x i;; jret <- x (j iret);; x (k jret)
  .
  Proof. i. Fail refl. my_red_both. refl. Qed.

  Goal forall T U V (i: itree _ T) (j: ktree _ T U) (k: ktree _ U V),
      y (x (i >>= j >>= k)) = iret <- y (x i);; jret <- y (x (j iret));; y (x (k jret))
  .
  Proof. i. Fail refl. my_red_both. refl. Qed.

  Goal forall T U V (i: itree _ T) (j: ktree _ T U) (k: ktree _ U V),
      z (y (x (i >>= j >>= k))) = iret <- z (y (x i));; jret <- z (y (x (j iret)));; z (y (x (k jret)))
  .
  Proof. i. Fail refl. my_red_both. refl. Qed.

  Goal forall T U V (j: ktree _ T U) (k: ktree _ U V),
      x (trigger (Choose _) >>= j >>= k) = iret <- trigger (Choose _);; iret <- (tau;; Ret iret);; jret <- x (j iret);; x (k jret)
  .
  Proof. i. Fail refl. my_red_both. refl. Qed.

  Goal forall T U (i: itree _ T) (j: ktree _ T U),
      y (x (tau;; i >>= j)) = tau;; y (x (i >>= j))
  .
  Proof. i. Fail refl. my_red_both. refl. Qed.

  Goal forall T U V (i: itree _ T) (j: ktree _ T U) (k: ktree _ U V),
      y (x (i >>= j >>= k)) = y (x (i >>= (j >>> k)))
  .
  Proof. i. Fail refl. my_red_both. Fail refl.
  (*** NOTE: We are normalizing ONLY THE HEAD on each layer. Is this what we really want?
             We may also normalize as much as we can on each layer.
             Which one is better? (in terms of performance, readability, etc)? ***)
  Abort.

  Variable xx: forall T, nat -> itree (eventE +' E) T -> nat -> itree (eventE +' F) T.

  Hypothesis xx_bind: forall R S i (k: ktree _ R S) p q, (xx p (i >>= k) q) = (r <- xx p i q;; xx p (k r) q).
  Hypothesis xx_tau: forall R p q (i: itree _ R), (xx p (tau;; i) q) = tau;; (xx p i q).
  Hypothesis xx_ret: forall R p q (i: R), (xx p (Ret i) q) = Ret i.
  Hypothesis xx_triggere: forall R p q (i: eventE R), (xx p (trigger i) q) = (trigger i >>= (fun r => tau;; Ret r)).
  Hypothesis xx_UB: forall R p q, (xx p triggerUB q) = (triggerUB: itree _ R).
  Hypothesis xx_NB: forall R p q, (xx p triggerNB q) = (triggerNB: itree _ R).
  Hypothesis xx_unwrapU: forall R p q (i: option R), (xx p (unwrapU i) q) = (unwrapU i).
  Hypothesis xx_unwrapN: forall R p q (i: option R), (xx p (unwrapN i) q) = (unwrapN i).
  Hypothesis xx_assume: forall P p q, (xx p (assume P) q) = assume P >>= (fun _ => tau;; Ret tt).
  Hypothesis xx_guarantee: forall P p q, (xx p (guarantee P) q) = guarantee P >>= (fun _ => tau;; Ret tt).
  Hypothesis xx_exxt: forall R p q (i0 i1: itree _ R), i0 = i1 -> (xx p i0 q) = (xx p i1 q).

  Global Program Instance xx_rdb: red_database (mk_box xx) :=
    mk_rdb
      1
      (mk_box (xx_bind))
      (mk_box (xx_tau))
      (mk_box (xx_ret))
      (mk_box (xx_triggere))
      (mk_box (xx_triggere))
      (mk_box (xx_triggere))
      (mk_box (xx_triggere))
      (mk_box (xx_UB))
      (mk_box (xx_NB))
      (mk_box (xx_unwrapU))
      (mk_box (xx_unwrapN))
      (mk_box (xx_assume))
      (mk_box (xx_guarantee))
      (mk_box (xx_exxt))
  .

  Goal forall p q T U V (i: itree _ T) (j: ktree _ T U) (k: ktree _ U V),
      xx p (i >>= j >>= k) q = iret <- xx p i q;; jret <- xx p (j iret) q;; xx p (k jret) q
  .
  Proof. i. Fail refl. my_red_both. refl. Qed.

End TEST.







(* (*** Natural Transformations with Reduction lemmas ***) *)
(* Module NTR. *)
(*   Class t (E F: Type -> Type) := mk { *)
(*     n:> itree (eventE +' E) ~> itree (eventE +' F); *)
(*     bind: forall R S i (k: ktree _ R S), (n (i >>= k)) = (r <- n i;; n (k r)); *)
(*     tau: forall R (i: itree _ R), (n (tau;; i)) = tau;; (n i); *)
(*     ret: forall R (i: R), (n (Ret i)) = Ret i; *)
(*     triggere: forall R (i: eventE R), (n (trigger i)) = (trigger i >>= (fun r => tau;; Ret r)); *)
(*     UB: forall R, (n triggerUB) = (triggerUB: itree _ R); *)
(*     NB: forall R, (n triggerNB) = (triggerNB: itree _ R); *)
(*     unwrapU: forall R (i: option R), (n (unwrapU i)) = (unwrapU i); *)
(*     unwrapN: forall R (i: option R), (n (unwrapN i)) = (unwrapN i); *)
(*     assume: forall P, (n (assume P)) = assume P >>= (fun _ => tau;; Ret tt); *)
(*     guarantee: forall P, (n (guarantee P)) = guarantee P >>= (fun _ => tau;; Ret tt); *)
(*     ext: forall R (i0 i1: itree _ R), i0 = i1 -> (n i0) = (n i1); *)
(*   } *)
(*   . *)
(*   (* Arguments n [_ _] _ [T]. *) *)
(*   Arguments n [_ _]. *)
(*   Arguments bind [_ _]. *)
(*   Arguments tau [_ _]. *)
(*   Arguments ret [_ _]. *)
(*   Arguments triggere [_ _]. *)
(*   Arguments UB [_ _]. *)
(*   Arguments NB [_ _]. *)
(*   Arguments unwrapU [_ _]. *)
(*   Arguments unwrapN [_ _]. *)
(*   Arguments assume [_ _]. *)
(*   Arguments guarantee [_ _]. *)
(*   Arguments ext [_ _]. *)
(* End NTR. *)
(* Coercion NTR.n: NTR.t >-> Funclass. *)



(* Section TEST. *)

(*   Variable E F G H: Type -> Type. *)
(*   Variable x: NTR.t E F. *)
(*   Variable y: NTR.t F G. *)
(*   Variable z: NTR.t G H. *)

(*   Let xn := NTR.n x. *)
(*   Let yn := NTR.n y. *)
(*   Let zn := NTR.n z. *)

(*   Global Program Instance x_rdb: red_database (mk_box xn) := *)
(*     mk_rdb *)
(*       (mk_box (NTR.bind x)) *)
(*       (mk_box (NTR.tau x)) *)
(*       (mk_box (NTR.ret x)) *)
(*       (mk_box (NTR.triggere x)) *)
(*       (mk_box (NTR.triggere x)) *)
(*       (mk_box (NTR.triggere x)) *)
(*       (mk_box (NTR.UB x)) *)
(*       (mk_box (NTR.NB x)) *)
(*       (mk_box (NTR.unwrapU x)) *)
(*       (mk_box (NTR.unwrapN x)) *)
(*       (mk_box (NTR.assume x)) *)
(*       (mk_box (NTR.guarantee x)) *)
(*       (mk_box (NTR.ext x)) *)
(*   . *)

(*   Global Program Instance y_rdb: red_database (mk_box yn) := *)
(*     mk_rdb *)
(*       (mk_box (NTR.bind y)) *)
(*       (mk_box (NTR.tau y)) *)
(*       (mk_box (NTR.ret y)) *)
(*       (mk_box (NTR.triggere y)) *)
(*       (mk_box (NTR.triggere y)) *)
(*       (mk_box (NTR.triggere y)) *)
(*       (mk_box (NTR.UB y)) *)
(*       (mk_box (NTR.NB y)) *)
(*       (mk_box (NTR.unwrapU y)) *)
(*       (mk_box (NTR.unwrapN y)) *)
(*       (mk_box (NTR.assume y)) *)
(*       (mk_box (NTR.guarantee y)) *)
(*       (mk_box (NTR.ext y)) *)
(*   . *)

(*   Global Program Instance z_rdb: red_database (mk_box zn) := *)
(*     mk_rdb *)
(*       (mk_box (NTR.bind z)) *)
(*       (mk_box (NTR.tau z)) *)
(*       (mk_box (NTR.ret z)) *)
(*       (mk_box (NTR.triggere z)) *)
(*       (mk_box (NTR.triggere z)) *)
(*       (mk_box (NTR.triggere z)) *)
(*       (mk_box (NTR.UB z)) *)
(*       (mk_box (NTR.NB z)) *)
(*       (mk_box (NTR.unwrapU z)) *)
(*       (mk_box (NTR.unwrapN z)) *)
(*       (mk_box (NTR.assume z)) *)
(*       (mk_box (NTR.guarantee z)) *)
(*       (mk_box (NTR.ext z)) *)
(*   . *)

(*   (* Ltac my_red_both := repeat (try (prw _red_lsim 2 0); try (prw _red_lsim 1 0)). *) *)
(*   Ltac my_red_both := (try (prw _red_gen 2 0); try (prw _red_gen 1 0); folder). *)

(*   Goal forall T U V (i: itree _ T) (j: ktree _ T U) (k: ktree _ U V), *)
(*       xn (i >>= j >>= k) = iret <- xn i;; jret <- xn (j iret);; xn (k jret) *)
(*   . *)
(*   Proof. i. Fail refl. my_red_both. refl. Qed. *)

(*   Goal forall T U V (i: itree _ T) (j: ktree _ T U) (k: ktree _ U V), *)
(*       yn (xn (i >>= j >>= k)) = iret <- yn (xn i);; jret <- yn (xn (j iret));; yn (xn (k jret)) *)
(*   . *)
(*   Proof. i. Fail refl. my_red_both. refl. Qed. *)

(*   Goal forall T U V (i: itree _ T) (j: ktree _ T U) (k: ktree _ U V), *)
(*       zn (yn (xn (i >>= j >>= k))) = iret <- zn (yn (xn i));; jret <- zn (yn (xn (j iret)));; zn (yn (xn (k jret))) *)
(*   . *)
(*   Proof. i. Fail refl. my_red_both. refl. Qed. *)

(*   Goal forall T U V (j: ktree _ T U) (k: ktree _ U V), *)
(*       xn (trigger (Choose _) >>= j >>= k) = iret <- trigger (Choose _);; iret <- (tau;; Ret iret);; jret <- xn (j iret);; xn (k jret) *)
(*   . *)
(*   Proof. i. Fail refl. my_red_both. refl. Qed. *)

(* End TEST. *)

End TEST.
