Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.

Set Implicit Arguments.
Set Typeclasses Depth 5.




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

  Definition unembed A {Σ} `{@GRA.inG A Σ} (a: URA.car (t:=Σ)): itree Es (URA.car (t:=A)) :=
    assume(forall n (NEQ: n <> GRA.inG_id), a n = URA.unit);;;
    Ret (eq_rect_r (@URA.car) (a GRA.inG_id) GRA.inG_prf)
  .

  Definition unembed2 {A Σ} `{@GRA.inG A Σ} (a: URA.car (t:=Σ)): itree Es (URA.car (t:=A)) :=
    n <- trigger (Choose _);;
    (if Nat.eq_dec GRA.inG_id n
     then Ret tt
     else  assume (a n = URA.unit);;; Ret tt);;;
    Ret (eq_rect_r (@URA.car) (a GRA.inG_id) GRA.inG_prf)
  .

End UNPADDING.
Arguments unembed _ {Σ H}.















(* Definition until (n: nat): list nat := mapi (fun n _ => n) (List.repeat tt n). *)


(*** TODO: move to Coqlib ***)
Definition map_fst A B C (f: A -> C): A * B -> C * B := fun '(a, b) => (f a, b).
Definition map_snd A B C (f: B -> C): A * B -> A * C := fun '(a, b) => (a, f b).


(** TODO: move to PCM.v **)
Declare Scope ra_scope.
Delimit Scope ra_scope with ra.
Notation " K ==> V' " := (URA.pointwise K V'): ra_scope.


















Definition is_zero (v: val): bool := match v with | Vint x => dec x 0%Z | _ => false end.


Require Import SimModSem.



Create HintDb stb.
Hint Rewrite (Seal.sealing_eq "stb"): stb.

Ltac stb_tac :=
  match goal with
  | [ |- alist_find _ ?xs = _ ] =>
    match type of xs with
    | (list (string * fspec)) =>
      autounfold with stb; autorewrite with stb; simpl
    end
  | [H: alist_find _ ?xs = _ |- _ ] =>
    match type of xs with
    | (list (string * fspec)) =>
      autounfold with stb in H; autorewrite with stb in H; simpl in H
    end
  end.



Inductive ltac_Wild : Set :=
| ltac_wild : ltac_Wild.
Notation "'__'" := ltac_wild : ltac_scope.
Open Scope ltac_scope.

Ltac on_first_hyp tac :=
  match reverse goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

Ltac idtacs Hs :=
  match Hs with
  | (?H0, ?H1) => idtacs H0; idtacs H1
  | ?H => idtac H
  end
.
