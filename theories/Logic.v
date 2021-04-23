Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.
Set Typeclasses Depth 5.



Section IRIS.
  Context {Σ: GRA.t}.
  Definition iProp := Σ -> Prop.
  Definition Sepconj (P Q: iProp): iProp :=
    fun r => exists a b, r = URA.add a b /\ P a /\ Q b
  .
  Definition Pure (P: Prop): iProp := fun _ => P.
  Definition Ex {X: Type} (P: X -> iProp): iProp := fun r => exists x, P x r.
  Definition Univ {X: Type} (P: X -> iProp): iProp := fun r => forall x, P x r.
  Definition Own (r0: Σ): iProp := fun r1 => URA.extends r0 r1.
  Definition And (P Q: iProp): iProp := fun r => P r /\ Q r.
  Definition Or (P Q: iProp): iProp := fun r => P r \/ Q r.
  Definition Wand (P Q: iProp): iProp := fun r => forall rp, URA.wf (r ⋅ rp) -> P rp -> Q (r ⋅ rp).
  Definition Upd (P: iProp): iProp := fun r0 => exists r1, forall ctx, URA.wf (r0 ⋅ ctx) -> URA.wf (r1 ⋅ ctx) /\ P r1.
  Definition Upd2 (P: iProp): iProp := fun r0 => forall ctx, URA.wf (r0 ⋅ ctx) -> exists r1, URA.wf (r1 ⋅ ctx) /\ P r1. (**** Iris version ****)
  (* Definition Own (r0: Σ): iProp := fun r1 => r0 = r1. *)

  Definition Entails (P Q: iProp): Prop := forall r (WF: URA.wf r), P r -> Q r.
  (* Definition Entails (P Q: iProp): Prop := P <1= Q. *)
  Definition Equiv (P Q: iProp): Prop := Entails P Q /\ Entails Q P.
  Definition Impure (P: iProp): Prop := Entails (Pure True) P.
  (* Definition Impure (P: iProp): Prop := P ε. *)
  (* Definition Impure (P: iProp): Prop := forall r, P r. *)
  (* Coercion Impure_coercion (P: iProp): Prop := Impure P. *)
  (* Coercion Impure_coercion := Impure. *)

End IRIS.

Infix "⊢" := Entails (at level 61).
Infix "⊣⊢" := Equiv (at level 60).
Infix "**" := Sepconj (at level 60).
Infix "∧" := And (at level 60).
Infix "∨" := Or (at level 60).
Infix "-*" := Wand (at level 60, right associativity).
Notation "'⌜' P '⌝'" := (Pure P).
Notation "'Exists' x .. y , p" := (Ex (fun x => .. (Ex (fun y => p)) ..))
                                    (at level 200, x binder, right associativity,
                                     format "'[' 'Exists'  '/  ' x  ..  y ,  '/  ' p ']'").
Notation "'Forall' x .. y , p" := (Univ (fun x => .. (Univ (fun y => p)) ..))
                                    (at level 200, x binder, right associativity,
                                     format "'[' 'Forall'  '/  ' x  ..  y ,  '/  ' p ']'").
Notation "|=> P" := (Upd P) (at level 60).
Notation "'⌞' P '⌟'" := (Impure P).





(* Section IRIS. *)
(*   Context {Σ: GRA.t}. *)
(*   Goal (⌜True⌝ -* ⌜False⌝ -* ⌜False⌝) ε. ii; et. Qed. *)
(*   Goal (⌜True⌝ ⊢ ⌜True⌝). ii; et. Qed. *)
(*   Goal (⌜True⌝ ⊢ ⌜False⌝ -* ⌜False⌝). ii; et. Qed. *)
(*   Goal (⌜True⌝ ⊢ ⌜False⌝ -* ⌜True⌝ -* ⌜False⌝). ii; et. Qed. *)

(*   Local Declare Scope iprop_scope. *)
(*   Local Declare Scope boo_scope. *)
(*   Infix "-#" := Wand (at level 60, right associativity): iprop_scope. *)
(*   Infix "-#" := Entails (at level 60, right associativity). *)
(*   Bind Scope iprop_scope with iProp. *)
(*   Bind Scope iprop_scope with iProp. *)
(*   Bind Scope iprop_scope with Σ. *)
(*   (* Local Open Scope iprop_scope. *) *)
(*   Fail Goal (⌜True⌝ -# ⌜False⌝ -# ⌜True⌝ -# ⌜False⌝). *)
(* End IRIS. *)




Section IRIS.
  Context {Σ: GRA.t}.

  Lemma Own_extends
        (a b: Σ)
        (EXT: URA.extends a b)
    :
      (Own b) <1= (Own a)
  .
  Proof. ii. ss. r in PR. r. etrans; et. Qed.

  (* Lemma Iff_eq *)
  (*       P Q *)
  (*       (IFF: P ⊣⊢ Q) *)
  (*   : *)
  (*     P = Q *)
  (* . *)
  (* Proof. *)
  (*   apply func_ext. i. apply prop_ext. r in IFF. des. split; i; et. *)
  (* Qed. *)

  Lemma own_sep'
        (r0 r1 r2: Σ)
        (ADD: r0 = r1 ⋅ r2)
    :
      Own r0 = Sepconj (Own r1) (Own r2)
  .
  Proof.
    apply func_ext. i. apply prop_ext.
    split; ii.
    - clarify. r in H. r. r in H. des. exists r1, (r2 ⋅ ctx). esplits; et.
      + rewrite URA.add_assoc. ss.
      + refl.
      + rr. esplits; et.
    - r in H. r. des. clarify. r in H0. r in H1. etrans.
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

  Lemma own_upd2
        (r1 r2: Σ)
        (UPD: URA.updatable r1 r2)
    :
      (Own r1) <1= (Upd2 (Own r2))
  .
  Proof.
    ii. r in UPD. rr in PR. des. subst. esplits; cycle 1.
    - rr. exists ε. rewrite URA.unit_id. refl.
    - specialize (UPD ctx). eapply UPD. eapply URA.wf_mon; et.
      rewrite <- URA.add_assoc in H. rewrite (URA.add_comm ctx0) in H. rewrite URA.add_assoc in H. et.
  Qed.

  Lemma own_upd2_set
        (r1: Σ) B
        (UPD: URA.updatable_set r1 B)
    :
      (Own r1) <1= (Upd2 (Exists b, ⌜B b⌝ ∧ (Own b)))
  .
  Proof.
    ii. r in UPD. rr in PR. des. subst. exploit UPD.
    { instantiate (1:=_ ⋅ _). rewrite URA.add_assoc. et. }
    i; des. rewrite URA.add_assoc in WF.
    eexists (b ⋅ ctx0).
    split; ss.
    rr. esplits; et. split; et. rr. esplits; et.
  Qed.

  Lemma own_upd
        (r1 r2: Σ)
        (UPD: URA.updatable r1 r2)
    :
      (Own r1) <1= (Upd (Own r2))
  .
  Proof.
    ii. r in UPD. rr in PR. des. subst. exists r2. i. esplits; cycle 1.
    - refl.
    - specialize (UPD ctx0). eapply UPD. eapply URA.wf_mon; et.
      rewrite <- URA.add_assoc in H. rewrite (URA.add_comm ctx) in H. rewrite URA.add_assoc in H. et.
  Qed.

  Lemma own_upd_set
        (r1: Σ) B
        (UPD: URA.updatable_set r1 B)
    :
      (Own r1) <1= (Upd (Exists b, ⌜B b⌝ ∧ (Own b)))
  .
  Proof.
    ii. r in UPD. rr in PR. des. subst. r. specialize (UPD ctx).
  Abort.

End IRIS.
