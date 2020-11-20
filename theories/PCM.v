Require Import sflib.
From Paco Require Import paco.
Require Import ClassicalDescription.
Require Import RelationClasses.
Require Import BinPos.
Require Import Lia.
(* Require Import Qcanon. *)
(* (*** from stdpp ***) *)
(* Record Qp : Set := mk_Qp { Qp_car : Qc;  Qp_prf : 0 < Qp_car }. *)



Ltac et := eauto.
Ltac func_ext := apply FunctionalExtensionality.functional_extensionality.
Ltac des_u := match goal with | [ a: unit |- _ ] => destruct a end.
Ltac etrans := etransitivity.

Module RA.
  Class class: Type := {
    t: Type;
    add: t -> t -> t;
    wf: t -> Prop;
    add_comm: forall a b, add a b = add b a;
    add_assoc: forall a b c, add a (add b c) = add (add a b) c;
    wf_mon: forall a b, wf (add a b) -> wf a;

    extends := fun a b => exists ctx, add a ctx = b;
    updatable := fun a b => forall ctx, wf (add a ctx) -> wf (add b ctx);
    updatable_set := fun a B => forall ctx (WF: wf (add a ctx)),
                         exists b, <<IN: B b>> /\ <<WF: wf (add b ctx)>>;
  }
  .

  Definition sub {M: class}: t -> t -> t -> Prop :=
    fun ab a b => ab = add a b
  .

  Definition refines {M: class}: t -> t -> Prop :=
    fun r_tgt r_src =>
      forall ctx, wf (add r_src ctx) -> wf (add r_tgt ctx)
  .

  Goal forall (M: class), extends <2= refines.
  Proof.
    ii. r in PR. des; clarify. rewrite add_comm in H. rewrite add_assoc in H.
    apply wf_mon in H. rewrite add_comm. ss.
  Qed.

  Goal forall (M: class), refines <2= extends.
  Proof.
    intros ? r_tgt r_src ?. r in PR; r.
    destruct (classic (exists diff, sub r_src r_tgt diff)).
    - des. r in H. subst. eauto.
    - Abort.

  Theorem update_horizontal
          (M: class)
          a0 a1
          b0 b1
          (UPDA: updatable a0 a1)
          (UPDB: updatable b0 b1)
    :
      <<UPD: updatable (add a0 b0) (add a1 b1)>>
  .
  Proof.
    ii. rewrite <- add_assoc in H. apply UPDA in H.
    rewrite add_comm in H. rewrite <- add_assoc in H.
    apply UPDB in H. rewrite add_comm with (a:=a1). rewrite <- add_assoc.
    rewrite add_comm with (a:=a1). eauto.
  Qed.

  Theorem update_vertical_stupid
          (M: class)
          a0 a1 a2
          (UPDA: forall ctx, (wf (add a0 ctx) -> wf (add a1 ctx)) /\ (wf (add a1 ctx) -> wf (add a2 ctx)))
    :
      <<UPD: updatable a0 a2>>
  .
  Proof.
    ii. specialize (UPDA ctx). des. eauto.
  Qed.

  Theorem update_stupid
          (M: class)
          a0 a1 a2
          b0 b1
          (UPDA: forall ctx, (wf (add a0 ctx) -> wf (add a1 ctx)) /\ (wf (add a1 ctx) -> wf (add a2 ctx)))
          (UPDB: updatable b0 b1)
    :
      <<UPD: updatable (add a0 b0) (add a2 b1)>>
  .
  Proof.
    ii. rewrite <- add_assoc in H.
    specialize (UPDA (add b0 ctx)).
    apply UPDA in H. apply UPDA in H.
    rewrite add_comm in H. rewrite <- add_assoc in H.
    apply UPDB in H. rewrite add_comm with (a:=a2). rewrite <- add_assoc.
    rewrite add_comm with (a:=a2). eauto.
  Qed.

  Program Instance extends_Transitive `{M: class}: Transitive extends.
  Next Obligation.
    rr. ii. rr in H. rr in H0. des. rewrite <- H0. rewrite <- H. esplits; et. rewrite add_assoc. et.
  Qed.

  Program Instance prod (M0 M1: class): class := {
    t := t (class:=M0) * t (class:=M1);
    add := fun '(a0, a1) '(b0, b1) => ((add a0 b0), (add a1 b1));
    wf := fun '(a0, a1) => wf a0 /\ wf a1;
  }
  .
  Next Obligation. f_equal; rewrite add_comm; ss. Qed.
  Next Obligation. f_equal; rewrite add_assoc; ss. Qed.
  Next Obligation. split; eapply wf_mon; et. Qed.

  Theorem prod_updatable
          M0 M1
          (a0: @t M0) (a1: @t M1)
          (b0: @t M0) (b1: @t M1)
          (UPD0: updatable a0 b0)
          (UPD1: updatable a1 b1)
    :
      <<UPD: @updatable (prod M0 M1) (a0, a1) (b0, b1)>>
  .
  Proof.
    ii. ss. des_ifs. des. esplits; et.
  Qed.

  Program Instance frac (denom: positive): class := {
    t := positive;
    add := fun a b => (a + b)%positive;
    wf := fun a => (a <= denom)%positive;
  }
  .
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.

  Theorem frac_updatable
          denom M
          a b
    :
      <<UPD: @updatable (prod (frac denom) M) (denom, a) b>>
  .
  Proof.
    ii. ss. des_ifs. des. lia.
  Qed.

  Program Instance agree (A: Type): class := {
    t := option A;
    add := fun a0 a1 => if excluded_middle_informative (a0 = a1) then a0 else None;
    wf := fun a => a <> None;
  }
  .
  Next Obligation. des_ifs. Qed.
  Next Obligation. des_ifs. Qed.
  Next Obligation. des_ifs. Qed.

  Theorem agree_unupdatable
          A
          a0 a1
    :
      <<UPD: @updatable (agree A) (Some a0) a1 -> a1 = Some a0>>
  .
  Proof.
    ii. ss. rr in H. specialize (H (Some a0)). ss. des_ifs. clear_tac.
    apply NNPP. ii. apply H; ss.
  Qed.

  Program Instance excl (A: Type): class := {
    t := option A;
    add := fun _ _ => None;
    wf := fun a => a <> None;
  }
  .

  Theorem excl_updatable
          A
          a0 a1
    :
      <<UPD: @updatable (excl A) (Some a0) a1>>
  .
  Proof. rr. ii. ss. Qed.

  (* Definition excl_map A B (f: A -> B) (a: option A + unit): option B + unit := *)
  (*   match a with *)
  (*   | inl oa => inl (option_map f oa) *)
  (*   | inr tt => inr tt *)
  (*   end *)
  (* . *)
  (* Instance exclC_Functor: Functor (fun A => @PCM.t (@RA.excl A)) := Build_Functor _ exclC_map. *)

  (*** exclusive <---> embracive ***)
  Program Instance embr (A: Type): class := {
    t := option A;
    add := fun _ _ => None;
    wf := fun _ => True;
  }
  .




  (* Definition boom := unit. *)
  (*** TODO: unify the style with auth_t: either use custom inductive, or just sum ***)

  (*** program instance act weirdly, so I put the definition out... ***)
  (*** TODO: fix it properly ***)
  Let sum_add {M0 M1} := (fun (a b: t (class:=M0) + t (class:=M1) + unit) =>
                            match a, b with
                            | inl (inl a0), inl (inl b0) => inl (inl (add a0 b0))
                            | inl (inr a1), inl (inr b1) => inl (inr (add a1 b1))
                            | _, _ => inr tt
                            end).
  Let sum_wf {M0 M1} := (fun (a: t (class:=M0) + t (class:=M1) + unit) =>
                           match a with
                           | inl (inl a0) => wf a0
                           | inl (inr a1) => wf a1
                           | _ => False
                           end).
  Program Instance sum (M0 M1: class): class := {
    t := t (class:=M0) + t (class:=M1) + unit (* boom *);
    add := sum_add;
    wf := sum_wf;
  }
  .
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_comm. Qed.
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_assoc. Qed.
  Next Obligation. unfold sum_wf in *. des_ifs; ss; des_ifs; eapply wf_mon; et. Qed.

  Program Instance pointwise K (M: class): class := {
    t := K -> t;
    add := fun f0 f1 => (fun k => add (f0 k) (f1 k));
    wf := fun f => forall k, wf (f k);
  }
  .
  Next Obligation. func_ext. ii. rewrite add_comm. ss. Qed.
  Next Obligation. func_ext. ii. rewrite add_assoc. ss. Qed.
  Next Obligation. eapply wf_mon; ss. Qed.

End RA.








(*** PCM == Unital RA ***)
(*** Whence URA, not RA? (1) Auth algebra (2) global RA construction ***)
Module PCM.
  Class class: Type := {
    t: Type;
    unit: t;
    add: t -> t -> t;
    wf: t -> Prop;
    add_comm: forall a b, add a b = add b a;
    add_assoc: forall a b c, add a (add b c) = add (add a b) c;
    unit_wf: wf unit;
    unit_id: forall a, add a unit = a;
    wf_mon: forall a b, wf (add a b) -> wf a;

    (* extends := fun a b => exists ctx, add a ctx = b; *)
    (* updatable := fun a b => forall ctx, wf (add a ctx) -> wf (add b ctx); *)
  }
  .

  Program Instance RA_of_PCM (M: class): RA.class := {
    RA.t := t;
    RA.add := add;
    RA.wf := wf;
  }
  .
  Next Obligation. apply add_comm. Qed.
  Next Obligation. apply add_assoc. Qed.
  Next Obligation. eapply wf_mon; et. Qed.

  Coercion RA_of_PCM: class >-> RA.class.

  Lemma unit_idl `{M: class}: forall a, add unit a = a. i. rewrite add_comm. rewrite unit_id; ss. Qed.

  Global Program Instance extends_PreOrder `{M: class}: PreOrder RA.extends.
  Next Obligation. rr. eexists unit. ss. rewrite unit_id. ss. Qed.

  Program Instance canonical_construction (RA: RA.class): class := {
    t := RA.t + Datatypes.unit;
    unit := inr tt;
    wf := fun a => match a with
                   | inl a => RA.wf a
                   | _ => True
                   end;
    add := fun a b =>
             match a, b with
             | inl a, inl b => inl (RA.add a b)
             | inr _, _ => b
             | _, inr _ => a
             end;
  }.
  Next Obligation. des_ifs. { rewrite RA.add_comm; ss. } { repeat des_u; ss. } Qed.
  Next Obligation. des_ifs. { rewrite RA.add_assoc; ss. } Qed.
  Next Obligation. des_ifs. { repeat des_u; ss. } Qed.
  Next Obligation. des_ifs. eapply RA.wf_mon; eauto. Qed.

  Inductive auth_t `{M: class}: Type :=
  | frag (f: t)
  | excl (e: t) (f: t)
  | boom
  .

  Program Instance auth (M: class): class := {
    t := auth_t;
    unit := frag unit;
    add := fun a0 a1 => match a0, a1 with
                        | frag f0, frag f1 => frag (add f0 f1)
                        | frag f0, excl e1 f1 => excl e1 (add f0 f1)
                        | excl e0 f0, frag f1 => excl e0 (add f0 f1)
                        | _, _ => boom
                        end;
    wf := fun a =>
            match a with
            | frag f => wf f
            | excl e f => RA.extends f e /\ wf e
            | boom => False
            end;
  }
  .
  Next Obligation. esplits; ii; des; ss. Qed.
  Next Obligation. esplits; ii; des; ss. Qed.
  Next Obligation. esplits; ii; des; ss. Qed.
  Next Obligation. esplits; ii; des; ss. Qed.
  Next Obligation. des_ifs; f_equal; eauto using add_comm. Qed.
  Next Obligation. des_ifs; f_equal; eauto using add_assoc. Qed.
  Next Obligation.
    eauto using unit_wf.
  Qed.
  Next Obligation.
    des_ifs; f_equal; eauto using unit_id.
  Qed.
  Next Obligation.
    des_ifs; des; eauto using wf_mon.
    - rr in H. des. subst. eapply wf_mon. rewrite add_assoc. eauto.
    - esplits; eauto. etrans; et. rr. ss. esplits; et.
  Qed.

  Definition black `{M: class} (a: t): t (class:=auth M) := excl a unit.
  Definition white `{M: class} (a: t): t (class:=auth M) := frag a.

  Theorem auth_dup_black
          `{M: class}
          a ca
          (CORE: a = add a ca)
    :
      <<DUP: RA.updatable (class:=auth M) (black a) (add (black a) (white ca))>>
  .
  Proof.
    rr. ii. des_ifs. rr in H. des. rewrite unit_idl in *. esplits; et.
    - rr. rr in H. des. esplits; et. ss. rewrite <- add_assoc. rewrite H. rewrite add_comm. eauto.
  Qed.

  Theorem auth_dup_white
          `{M: class}
          a ca
          (CORE: a = add a ca)
    :
      <<DUP: RA.updatable (class:=auth M) (white a) (add (white a) (white ca))>>
  .
  Proof.
    rr. ii. des_ifs.
    - ss. rewrite <- CORE. ss.
    - ss. des. esplits; et. rewrite <- CORE. ss.
  Qed.

  Theorem auth_spec
          `{M: class}
          a b
          (WF: wf (add (black a) (white b)))
    :
      <<EXT: RA.extends b a>>
  .
  Proof.
    rr in WF. des. rr in WF. rr. des. rewrite add_comm in WF. ss. rewrite unit_id in WF. subst.
    esplits; et.
  Qed.

End PCM.



(***
Choose: non-det
Take: angelic non-det
(*** empty choose : NB ***)
(*** empty take : UB ***)
x <- Choose X ;; guarantee (P x) ;; k x   (~=) x <- Choose { X | P x } ;; k x
x <- Take X   ;; assume (P x)    ;; k x   (~=) x <- Take { X | P x }   ;; k x
guarantee P ;; assume P ;; k              (~=) guarantee P ;; k
x <- Take X ;; pure ;; k x                (>=) pure ;; x <- Take X ;; k x
pure ;; x <- Choose X ;; k x              (>=) x <- Choose X ;; pure ;; k x
______________caller______________    _________________callee_________________   _caller_
x0 <- Choose X ;; guarantee (P x0) ;; (x1 <- Take X ;; assume (P x1) ;; k1 x1) ;; k0 x0
(<=)
x0 <- Choose X ;; x1 <- Take X ;; guarantee (P x0) ;; assume (P x1) ;; k1 x1 ;; k0 x0
(<=)
x <- Choose X ;; guarantee (P x) ;; assume (P x) ;; k1 x ;; k0 x
(<=)
x <- Choose X ;; guarantee (P x) ;; k1 x ;; k0 x
Goal forall X Y (k: X -> Y),
    x <- trigger (EChoose X) ;; Ret (k x) =
    y <- trigger (EChoose {y | exists x, y = k x}) ;; Ret (proj1_sig y)
.
Abort.
***)
