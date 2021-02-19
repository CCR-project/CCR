Require Import Coqlib.
Require Import Coq.Logic.IndefiniteDescription.

Set Implicit Arguments.


Module Type ANY.

  Parameter t: Type.
  Parameter ty: t -> Type.
  Parameter val: forall (a: t), (ty a).
  Parameter upcast: forall {T: Type}, T -> t.
  Parameter downcast: forall {T: Type}, t -> option T.
  (* Parameter downcast_fst: forall {T: Type}, t -> option (T * t). *)

  Parameter upcast_inj: forall A B (a: A) (b: B) (EQ: upcast a = upcast b),
      <<EQ: A = B>> /\ <<EQ: a ~= b>>.
  (* Parameter upcast_surj: forall A B a b (EQ: A = B) (EQ: a ~= b), *) (*** <-- this is trivial ***)
  (*     <<EQ: @upcast A a = @upcast B b>>. *)

  Parameter upcast_downcast: forall T (a: T), downcast (upcast a) = Some a.
  (* Parameter downcast_intro: forall (a: t), @downcast (ty a) a = Some (val a). *)
  Parameter downcast_intro: forall (a: t) T (v: T) (TY: (ty a) = T) (VAL: (val a) ~= v), downcast a = Some v.
  Parameter downcast_elim: forall (a: t) T (v: T) (CAST: downcast a = Some v), (<<TY: (ty a) = T>>) /\ (<<VAL: (val a) ~= v>>).
  Parameter upcast_eta: forall (a: t), <<CAST: a = upcast (val a)>>.
  Parameter upcast_elim: forall X (x: X), <<TY: ty (upcast x) = X>> /\ <<VAL: val (upcast x) ~= x>>.
  (* Parameter downcast_ty: forall (a: t), exists x, @downcast (ty a) a = Some x. *)

  (* Parameter patmat: forall R (body: forall (T: Type), T -> R), t -> R. *)
  (* Parameter patmat_spec: forall R (body: forall (T: Type), T -> R) *)
  (*                               T (t: T), (patmat body (upcast t): R) = body _ t. *)

End ANY.


Module _Any: ANY.

  Record _t := _upcast { ty: Type; val: ty }.
  Definition t := _t.

  Definition upcast := @_upcast.
  Arguments _upcast {ty}.
  Arguments upcast {ty}.

  Definition downcast {T: Type} (a: t): option T.
    destruct a.
    destruct (excluded_middle_informative (ty0 = T)).
    - subst. apply Some. assumption.
    - apply None.
  Defined.

  Lemma downcast_elim
        a T (v: T)
        (CAST: downcast a = Some v)
    :
      <<TY: a.(ty) = T>> /\ <<VAL: a.(val) ~= v>>
  .
  Proof.
    unfold downcast in *. des_ifs. ss.
    simpl_depind. eauto.
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

  Lemma upcast_elim: forall X (x: X), <<TY: ty (upcast x) = X>> /\ <<VAL: val (upcast x) ~= x>>.
  Proof. i. ss. Qed.

  Definition downcast_fst {T: Type} (a: t): option (T * t).
    destruct a.
    destruct (excluded_middle_informative (exists d, ty0 = (T * d)%type)).
    - apply constructive_indefinite_description in e. destruct e. subst. destruct val0.
      apply (Some (t0, upcast x)).
    - apply None.
  Defined.

  Definition pair (a b: t): t := upcast (val a, val b).
  Lemma type_pair_elim: forall (A B C: Type), (A * B)%type = (A * C)%type -> B = C.
  Proof.
    i.
    assert(eq_JMeq: forall B (b0 b1: B) (eq: b0 = b1), b0 ~= b1).
    { i; subst. refl. }
    assert(apply_f: forall A B (a0 a1: A) (f: A -> B), a0 = a1 -> f a0 = f a1).
    { ii; clarify. }
    assert(prod_elim: forall A B (ab0 ab1: prod A B), ab0 = ab1 -> fst ab0 = fst ab1 /\ snd ab0 = snd ab1).
    { destruct ab0, ab1; ss. i; clarify. }
    Fail eapply prod_elim in H.
    (* Set Printing All. *)
    assert(T: (A * B)%type = (A * B)%type) by ss.
    assert(U: (A * C)%type = (A * C)%type) by ss.
    Fail eapply (apply_f) with (f:=fst) in T.
    (* instantiate (1:=fst) in T. *)
  Abort.

  Inductive typrod {A B: Type}: Type :=
  | typair: 

  Lemma downcast_fst_spec
        X (x: X) (a: t)
    :
      downcast_fst (pair (upcast x) a) = Some (x, a)
  .
  Proof.
    unfold pair. unfold downcast_fst. des_ifs.
    - des. unfold eq_rect_r.
      unfold eq_rect in *.
      unfold eq_sym. des_ifs.
      f_equal. f_equal.
      + assert(ty a = x0).
        { destruct a; ss. clear - Heq.
          unfold upcast in *.
          (* Set Printing All. *)
          injection Heq. i.
          assert(eq_JMeq: forall B (b0 b1: B) (eq: b0 = b1), b0 ~= b1).
          { i; subst. refl. }
          (* assert(apply_f: forall A B (a0 a1: A) (f: A -> B), a0 ~= a1 -> f a0 = f a1). *)
          assert(apply_f: forall A B (a0 a1: A) (f: A -> B), a0 = a1 -> f a0 = f a1).
          { ii; clarify. }
          assert(ty0 = x0).
          { admit "somehow". }
          exploit apply_f; try apply Heq.
          Set Printing All.
          rewrite H.
          { instantiate (1:={| ty := X * ty0; val := (x, val0) |}). instantiate (1:={| ty := X * x0; val := (x1, x2) |}).
            apply eq_JMeq. ss. }
          instantiate (1:=fst).
            apply JMeq_eq.
            ss.
          eapply JMeq_eq. Set Printing All. instantiate (1:=fst).
          apply apply_f with (f:=fst) in Heq.
          subst. clear - e. }
        ss. unfold upcast in *. dependent destruction Heq.
    -
  Qed.

End _Any.
Goal _Any.upcast 0 = _Any.upcast () -> False. i. Fail injection H. Abort.



Module Any.
  Include _Any.
  Definition pair (a b: Any.t): Any.t := Any.upcast (Any.val a, Any.val b).
  
  (* Definition downcast_fst {T: Type} (a: t): option (T * t). *)
  (*   destruct a. *)
  (*   destruct (excluded_middle_informative (exists d, ty0 = (T * d)%type)). *)
  (*   - apply constructive_indefinite_description in e. destruct e. subst. destruct val0. *)
  (*     apply (Some (t0, upcast x)). *)
  (*   - apply None. *)
  (* Defined. *)
  Definition downcast_fst {T: Type} (a: t): option (T * t).
    destruct (excluded_middle_informative (exists d, (Any.ty a) = (T * d)%type)).
    - apply constructive_indefinite_description in e. destruct e. subst.
      set (v:=val a). rewrite e in *. destruct v.
      apply (Some (t0, upcast x0)).
    - apply None.
  Defined.

  Lemma downcast_fst_spec
        X (x: X) (a: Any.t)
    :
      downcast_fst (Any.pair (upcast x) a) = Some (x, a)
  .
  Proof.
    unfold pair. unfold downcast_fst. des_ifs.
    - des. f_equal.
      unfold eq_rect in *.
      destruct e0.
      dependent destruction e0.

      {
      hexploit (upcast_elim x); et. i; des.
      assert(eq_JMeq: forall B (b0 b1: B) (eq: b0 = b1), b0 ~= b1).
      { i; subst. refl. }
      exploit eq_JMeq; try apply e. intro P.
      Unset Universe Checking.
      rewrite VAL in P.
      hexploit (upcast_elim (x, val a)); et. i; des.
      rewrite TY0 in P. apply JMeq_eq in P. destruct P.
      rewrite <- upcast_eta in *. assert(d = x0). { clear - e e0. rewrite e in *. clear - e0. remember (prod X d) as A. remember (prod X x0) as B. }
  Qed.

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
