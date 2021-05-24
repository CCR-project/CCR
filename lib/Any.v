Require Import Coqlib.
From Ordinal Require Import Ordinal.

Set Implicit Arguments.


Module Type ANY.

  Parameter t: Type.
  Parameter ty: t -> Type.
  Parameter val: forall (a: t), (ty a).
  Parameter upcast: forall {T: Type}, T -> t.
  Parameter downcast: forall {T: Type}, t -> option T.
  Parameter pair: t -> t -> t.

  Parameter upcast_inj: forall A B (a: A) (b: B) (EQ: upcast a = upcast b),
      <<EQ: A = B>> /\ <<EQ: a ~= b>>.
  (* Parameter upcast_surj: forall A B a b (EQ: A = B) (EQ: a ~= b), *) (*** <-- this is trivial ***)
  (*     <<EQ: @upcast A a = @upcast B b>>. *)

  Parameter upcast_downcast: forall T (v: T), downcast (upcast v) = Some v.
  (* Parameter downcast_intro: forall (a: t), @downcast (ty a) a = Some (val a). *)
  Parameter downcast_intro: forall (a: t) T (v: T) (TY: (ty a) = T) (VAL: (val a) ~= v), downcast a = Some v.
  Parameter downcast_elim: forall (a: t) T (v: T) (CAST: downcast a = Some v), (<<TY: (ty a) = T>>) /\ (<<VAL: (val a) ~= v>>).
  Parameter upcast_eta: forall (a: t), <<CAST: a = upcast (val a)>>.
  Parameter downcast_upcast: forall T (v: T) (a: t), downcast a = Some v -> <<CAST: upcast v = a>>.
  (* Parameter downcast_ty: forall (a: t), exists x, @downcast (ty a) a = Some x. *)

  (* Parameter patmat: forall R (body: forall (T: Type), T -> R), t -> R. *)
  (* Parameter patmat_spec: forall R (body: forall (T: Type), T -> R) *)
  (*                               T (t: T), (patmat body (upcast t): R) = body _ t. *)

  Parameter upcast_pair_downcast: forall A B (a: A) (b: B), downcast (pair (upcast a) (upcast b)) = Some (a, b).
  Parameter pair_downcast: forall X Y (a0 a1: t) (x: X) (y: Y),
      downcast (pair a0 a1) = Some (x, y) -> a0 = (upcast x) /\ a1 = (upcast y).

End ANY.


Module _Any: ANY.

  Record _t := _upcast { ty: Type; val: ty }.
  Definition t := _t.

  Section FOO.
    Let _foo: _t := _upcast Ord.O.
  End FOO.

  Definition upcast := @_upcast.
  Arguments _upcast {ty}.
  Arguments upcast {ty}.

  Definition downcast {T: Type} (a: t): option T :=
    match (excluded_middle_informative (a.(ty) = T)) with
    | left e =>
      Some (match e in (_ = y0) return ((fun X => X) y0) with
            | eq_refl => a.(val)
            end)
    | right _ => None
    end.

(*   Definition downcast2 {T: Type} (a: t): option T. *)
(*     destruct a. *)
(*     destruct (excluded_middle_informative (ty0 = T)). *)
(*     - subst. apply Some. assumption. *)
(*     - apply None. *)
(*   Defined. *)
(* downcast2 =  *)
(* fun (T : Type) (a : t) => *)
(* match a with *)
(* | {| ty := ty0; val := val0 |} => *)
(*     let s := excluded_middle_informative (ty0 = T) in *)
(*     match s with *)
(*     | left e => eq_rect_r (fun ty1 : Type => ty1 -> option T) (fun val1 : T => Some val1) e val0 *)
(*     | in_right => None *)
(*     end *)
(* end *)
(*      : forall T : Type, t -> option T *)
  Lemma downcast_elim
        a T (v: T)
        (CAST: downcast a = Some v)
    :
      <<TY: a.(ty) = T>> /\ <<VAL: a.(val) ~= v>>
  .
  Proof.
    unfold downcast in *. des_ifs.
  Qed.

  Lemma downcast_intro
        a T (v: T)
        (TY: a.(ty) = T)
        (VAL: a.(val) ~= v)
    :
      <<CAST: downcast a = Some v>>
  .
  Proof.
    unfold downcast in *. des_ifs. ss.
    dependent destruction e. ss.
  Qed.
  (* Lemma downcast_intro: forall (a: t), @downcast (ty a) a = Some (val a). *)
  (* Proof. i. unfold downcast in *. des_ifs. ss. dependent destruction e; ss. Qed. *)

  Lemma upcast_downcast
        T (a: T)
    :
      downcast (upcast a) = Some a
  .
  Proof.
    eapply downcast_intro; ss.
  Qed.

  (* Lemma upcast_downcast_adjoint *)
  (*       (a: t) T (t: T) *)
  (*   : *)
  (*     <<UPCAST: a = upcast t>> <-> <<DOWNCAST: downcast a = Some t>> *)
  (* . *)
  (* Proof. *)
  (*   split; ii; des. *)
  (*   - clarify. rewrite upcast_downcast. ss. *)
  (*   - apply downcast_elim in H. des. r. *)
  (*     rewrite upcast_intro with a. simpl_depind. f_equal. ss. *)
  (* Qed. *)

  (* Definition dec (a0 a1: t): {a0=a1} + {a0<>a1}. *)
  (*   destruct a0, a1. *)
  (*   destruct (excluded_middle_informative (ty0 = ty1)). *)
  (*   - clarify. *)
  (*     destruct (excluded_middle_informative (val0 = val1)). *)
  (*     + clarify. left. ss. *)
  (*     + right. ii. simpl_depind. clarify. *)
  (*   - right. ii. simpl_depind. *)
  (* Defined. *)


  Lemma upcast_ty
        A (a: A)
    :
      <<EQ: (upcast a).(ty) = A>>
  .
  Proof. ss. Qed.

  Lemma upcast_val
        A (a: A)
    :
      <<EQ: (upcast a).(val) = a>>
  .
  Proof. ss. Qed.

  Lemma upcast_eta
        (a: t)
    :
      <<CAST: a = upcast (a.(val))>>
  .
  Proof. destruct a; ss. Qed.




  Lemma upcast_inj
        A B (a: A) (b: B)
        (EQ: upcast a = upcast b)
    :
      <<EQ: A = B>> /\ <<EQ: a ~= b>>
  .
  Proof. unfold upcast in *. simpl_depind. ss. Qed.

  (*** epimorphism? ***)
  (* Lemma upcast_surj *)
  (*       (a0 a1: t) *)
  (*       (EQTY: a0.(ty) = a1.(ty)) *)
  (*       (EQVAL: a0.(val) ~= a1.(val)) *)
  (*   : *)
  (*     <<EQ: a0 = a1>> *)
  (* . *)
  (* Proof. destruct a0, a1; ss. clarify. Qed. *)

  Lemma upcast_surj
        A B a b
        (EQTY: A = B)
        (EQVAL: a ~= b)
    :
      <<EQ: @upcast A a = @upcast B b>>
  .
  Proof. clarify. Qed.

  (* Definition patmat: forall R (body: forall (T: Type), T -> R), t -> R. *)
  (*   i. destruct X. apply (body ty0 val0). Defined. *)
  (* Lemma patmat_spec: forall R (body: forall (T: Type), T -> R) *)
  (*                           T (t: T), (patmat body (upcast t): R) = body _ t. *)
  (* Proof. ss. Qed. *)

  Lemma downcast_ty: forall (a: t), exists x, @downcast (ty a) a = Some x.
  Proof.
    i. exists a.(val). rewrite <- upcast_downcast. f_equal.
    destruct a. refl.
  Qed.

  Lemma downcast_upcast: forall T (v: T) (a: t), downcast a = Some v -> <<CAST: upcast v = a>>.
  Proof.
    i. unfold upcast, downcast in *. des_ifs. destruct a; ss.
  Qed.

  (* Inductive myprod (A B: Type): Type := mypair: A -> B -> myprod A B. *)
  (* Definition pair (a b: t): t := upcast (mypair (val a) (val b)). *)
  Definition pair (a b: t): t := upcast ((val a), (val b)).

  Lemma upcast_pair_downcast: forall A B (a: A) (b: B),
      <<CAST: downcast (pair (upcast a) (upcast b)) = Some (a, b)>>.
  Proof.
    i. unfold downcast. des_ifs. ss. r. f_equal.
    Local Set Printing Universes.
    set (A: Type@{downcast.u1}) as AA. ss.
    set (B: Type@{downcast.u1}) as BB. ss.
    folder.
    dependent destruction e.
    ss.
  Qed.

  Lemma pair_downcast: forall X Y (a0 a1: t) (x: X) (y: Y),
      downcast (pair a0 a1) = Some (x, y) -> a0 = (upcast x) /\ a1 = (upcast y).
  Proof.
    i.
    unfold downcast in *.
    des_ifs. ss. dependent destruction e. clarify.
    unfold upcast. destruct a0, a1; ss.
  Qed.
  Require Import String.
  Lemma pair_downcast: forall (a0 a1: t) (x: ty a0) (y: ty a1),
      downcast (pair a0 a1) = Some (x, y) -> a0 = (upcast x) /\ a1 = (upcast y).
  Proof.
    i.
    unfold downcast in *.
    des_ifs. ss. dependent destruction e. clarify.
    unfold upcast. destruct a0, a1; ss.
  Qed.

End _Any.
Goal _Any.upcast 0 = _Any.upcast () -> False. i. Fail injection H. Abort.



Module Any.
  Include _Any.
  Definition pair (a b: Any.t): Any.t := Any.upcast (Any.val a, Any.val b).
End Any.

(* Notation "↑ a" := (Any.upcast a) (at level 60, only parsing). *)
(* Notation "↓ a" := (Any.downcast a) (at level 60, only parsing). *)
(* Goal (↓↑ tt) = Some tt. rewrite Any.upcast_downcast. ss. Qed. *)
(* Check (Any.pair ↑tt ↑tt). *)
Notation "a ↑" := (Any.upcast a) (at level 9, only parsing).
Notation "a ↓" := (Any.downcast a) (at level 9, only parsing).
Notation "(↑)" := (Any.upcast) (only parsing).
Notation "(↓)" := (Any.downcast) (only parsing).
Goal (tt↑↓) = Some tt. rewrite Any.upcast_downcast. ss. Qed.
Check (Any.pair tt↑ tt↑).
