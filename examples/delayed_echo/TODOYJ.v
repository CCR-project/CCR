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

Section EXTEND.

  Context `{Σ: GRA.t}.

  Definition extends (stb0 stb1: list (string * fspec)): Prop :=
    forall fn fnf (FIND: List.find (fun '(_fn, _) => dec fn _fn) stb0 = Some fnf),
      List.find (fun '(_fn, _) => dec fn _fn) stb1 = Some fnf.

  Global Program Instance extends_PreOrder: PreOrder extends.
  Next Obligation.
  Proof.
    ii. auto.
  Qed.
  Next Obligation.
  Proof.
    ii. eapply H in FIND. eapply H0 in FIND. auto.
  Qed.

  Lemma nodup_incl_extends stb0 stb1
        (INCL: List.incl stb0 stb1)
        (NODUP: NoDup (List.map fst stb1))
    :
      extends stb0 stb1.
  Proof.
  Admitted.

  (* Lemma modsempair_extends (md_tgt md_src0 md_src1: ModSemL.t) *)
  (*         sbtb stb0 stb1 initial_mrs *)
  (*         (SIM: ModSemLPair.sim (ModSemL.mk (List.map (fun '(fn, fsb) => (fn, fun_to_tgt stb1 fn fsb)) sbtb) initial_mrs) md_tgt) *)
  (*         (EXTENDS: extends stb0 stb1) *)
  (*   : *)
  (*     ModSemLPair.sim (ModSemL.mk (List.map (fun '(fn, fsb) => (fn, fun_to_tgt stb0 fn fsb)) sbtb) initial_mrs) md_tgt. *)
  (* Proof. *)
  (*   inv SIM. econs. *)
  (*   { eapply le_PreOrder. } *)
  (*   { instantiate (1:=wf). simpl in *. revert sim_fnsems. *)
  (*     generalize (ModSemL.fnsems md_tgt). induction sbtb. *)
  (*     { i. inv sim_fnsems. econs. } *)
  (*     i. destruct a as [fn fb]. inv sim_fnsems. simpl in *. econs. *)
  (*     2: { eapply IHsbtb. auto. } *)
  (*     destruct y as [fn' tr]. inv H1. econs. *)
  (*     { unfold RelationPairs.RelCompFun in *. simpl in *. subst. auto. } *)
  (*     { unfold RelationPairs.RelCompFun in *. simpl in *. subst. ii. *)
  (*       exploit H0; [apply H|apply SIMMRS|]. i. des. exists n. *)
  (*       clear - EXTENDS x0. revert x0. *)
  (* Admitted. *)

End EXTEND.



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
