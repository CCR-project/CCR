Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.
Set Typeclasses Depth 5.




Global Opaque GRA.to_URA.
Infix "⋅" := URA.add (at level 50, left associativity).
Notation "(⋅)" := URA.add (only parsing).


Definition unleftU {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
  match xy with
  | inl x => Ret x
  | inr y => triggerUB
  end.

Definition unleftN {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
  match xy with
  | inl x => Ret x
  | inr y => triggerNB
  end.

Definition unrightU {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
  match xy with
  | inl x => triggerUB
  | inr y => Ret y
  end.

Definition unrightN {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
  match xy with
  | inl x => triggerNB
  | inr y => Ret y
  end.

Section UNPADDING.
  
  Definition unpadding A {Σ} `{@GRA.inG A Σ} (a: URA.car (t:=Σ)): itree Es (URA.car (t:=A)) :=
    assume(forall n (NEQ: n <> GRA.inG_id), a n = URA.unit);;
    Ret (eq_rect_r (@URA.car) (a GRA.inG_id) GRA.inG_prf)
  .

  Definition unpadding2 {A Σ} `{@GRA.inG A Σ} (a: URA.car (t:=Σ)): itree Es (URA.car (t:=A)) :=
    n <- trigger (Choose _);;
    (if Nat.eq_dec GRA.inG_id n
     then Ret tt
     else  assume (a n = URA.unit);; Ret tt);;
    Ret (eq_rect_r (@URA.car) (a GRA.inG_id) GRA.inG_prf)
  .

End UNPADDING.
Arguments unpadding _ {Σ H}.
















Section PROOF.
  Context {Σ: GRA.t}.
  (*** TODO: move to proper place, together with "mk_simple" ***)
  (*** TODO: rename sb into spb ***)
  (*** TODO: remove redundancy with Hoareproof0.v ***)
  Definition mk_simple (mn: string) {X: Type} (P: X -> Any.t -> ord -> Σ -> Prop) (Q: X -> Any.t -> Σ -> Prop): fspec :=
    @mk _ mn X (list val) (val) (fun x y a r o => P x a o r /\ y↑ = a) (fun x z a r => Q x a r /\ z↑ = a)
  .
  Definition mk_sb_simple (mn: string) {X: Type} (P: X -> Any.t -> ord -> Σ -> Prop) (Q: X -> Any.t -> Σ -> Prop)
             (body: list val -> itree (hCallE +' pE +' eventE) val): fspecbody := mk_specbody (mk_simple mn P Q) body.

End PROOF.






Section IRIS.
  Context {Σ: GRA.t}.
  Definition iProp := Σ -> Prop.
  Definition Sepconj (P Q: iProp): iProp :=
    fun r => exists a b, r = URA.add a b /\ P a /\ Q b
  .
  Definition Pure (P: Prop): iProp := fun _ => P.
  Definition Ex {X: Type} (P: X -> iProp): iProp := fun r => exists x, P x r.
  Definition Own (r0: Σ): iProp := fun r1 => URA.extends r0 r1.
  (* Definition Own (r0: Σ): iProp := fun r1 => r0 = r1. *)

  Definition Impl (P Q: iProp): Prop := P <1= Q.
  Infix "i->" := Impl (at level 60).
  Notation "P 'i<->' Q" := ((Impl P Q) /\ (Impl Q P)) (at level 60).

  Lemma Own_extends
        (a b: Σ)
        (EXT: URA.extends a b)
    :
      (Own b) i-> (Own a)
  .
  Proof. ii. ss. r in PR. r. etrans; et. Qed.

  Lemma Iff_eq
        P Q
        (IFF: P i<-> Q)
    :
      P = Q
  .
  Proof.
    apply func_ext. i. apply prop_ext. des. split; i; et.
  Qed.

  Lemma own_sep'
        (r0 r1 r2: Σ)
        (ADD: r0 = r1 ⋅ r2)
    :
      Own r0 = Sepconj (Own r1) (Own r2)
  .
  Proof.
    apply Iff_eq.
    split; ii.
    - clarify. r in PR. r. r in PR. des. exists r1, (r2 ⋅ ctx). esplits; et.
      + rewrite URA.add_assoc. ss.
      + refl.
      + rr. esplits; et.
    - r in PR. r. des. clarify. r in PR0. r in PR1. etrans.
      { eapply URA.extends_add; et. }
      rewrite ! (URA.add_comm a).
      eapply URA.extends_add; et.
  Qed.

  Lemma own_sep
        (r1 r2: Σ)
    :
      Own (r1 ⋅ r2) = Sepconj (Own r1) (Own r2)
  .
  Proof.
    erewrite <- own_sep'; et.
  Qed.

End IRIS.

Infix "**" := Sepconj (at level 60).
Notation "'⌜' P '⌝'" := (Pure P).
Notation "'Exists' x .. y , p" := (Ex (fun x => .. (Ex (fun y => p)) ..))
                                    (at level 200, x binder, right associativity,
                                     format "'[' 'Exists'  '/  ' x  ..  y ,  '/  ' p ']'").














(* Definition until (n: nat): list nat := mapi (fun n _ => n) (List.repeat tt n). *)


(*** TODO: move to Coqlib ***)
Definition map_fst A B C (f: A -> C): A * B -> C * B := fun '(a, b) => (f a, b).
Definition map_snd A B C (f: B -> C): A * B -> A * C := fun '(a, b) => (a, f b).


(** TODO: move to PCM.v **)
Declare Scope ra_scope.
Delimit Scope ra_scope with ra.
Notation " K ==> V' " := (URA.pointwise K V'): ra_scope.

