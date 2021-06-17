Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import ProofMode.

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



(*** TODO: move to Coqlib ***)
Definition map_fst A B C (f: A -> C): A * B -> C * B := fun '(a, b) => (f a, b).
Definition map_snd A B C (f: B -> C): A * B -> A * C := fun '(a, b) => (a, f b).


(** TODO: move to PCM.v **)
Declare Scope ra_scope.
Delimit Scope ra_scope with ra.
Notation " K ==> V' " := (URA.pointwise K V'): ra_scope.



Definition is_zero (v: val): bool := match v with | Vint x => dec x 0%Z | _ => false end.

Ltac on_first_hyp tac :=
  match reverse goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

Ltac idtacs Hs :=
  match Hs with
  | (?H0, ?H1) => idtacs H0; idtacs H1
  | ?H => idtac H
  end
.

Notation "(∘)" := (fun g f => g ∘ f) (at level 0, left associativity).

Variant option_rel A B (P: A -> B -> Prop): option A -> option B -> Prop :=
| option_rel_some
    a b (IN: P a b)
  :
    option_rel P (Some a) (Some b)
| option_rel_none
  :
    option_rel P None None
.
Hint Constructors option_rel: core.

Definition map_or_else X Y (ox: option X) (f: X -> Y) (d: Y) :=
  match ox with | Some x => f x | None => d end.

Lemma map_or_else_same: forall X Y (ox: option X) (d: Y), map_or_else ox (fun _ => d) d = d.
  i. destruct ox; ss.
Qed.

Definition or_else X (ox: option X) (d: X) := match ox with | Some x => x | None => d end.

Lemma map_or_else_id: forall X ox (d: X), map_or_else ox id d = or_else ox d. refl. Qed.




Section AUX.
  Context {K: Type} `{M: URA.t}.
  Let RA := URA.pointwise K M.

  Lemma pw_extends (f0 f1: K -> M) (EXT: @URA.extends RA f0 f1): <<EXT: forall k, URA.extends (f0 k) (f1 k)>>.
  Proof. ii. r in EXT. des. subst. ur. ss. eexists; et. Qed.

  Lemma pw_wf: forall (f: K -> M) (WF: URA.wf (f: @URA.car RA)), <<WF: forall k, URA.wf (f k)>>.
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

  Lemma pw_add_disj_wf
        (f g: K -> M)
        (WF0: URA.wf (f: @URA.car RA))
        (WF1: URA.wf (g: @URA.car RA))
        (DISJ: forall k, <<DISJ: f k = ε \/ g k = ε>>)
    :
      <<WF: URA.wf ((f: RA) ⋅ g)>>
  .
  Proof.
    ii; ss. ur. i. ur in WF0. ur in WF1. spc DISJ. des; rewrite DISJ.
    - rewrite URA.unit_idl; et.
    - rewrite URA.unit_id; et.
  Qed.

  Lemma pw_insert_wf: forall `{EqDecision K} (f: K -> M) k v (WF: URA.wf (f: @URA.car RA)) (WFV: URA.wf v),
      <<WF: URA.wf (<[k:=v]> f: @URA.car RA)>>.
  Proof.
    i. unfold insert, fn_insert. ur. ii. des_ifs. ur in WF. eapply WF.
  Qed.

End AUX.
