Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic YPM.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.





Ltac iIntros :=
  i;
  match goal with
  | |- Impure ?P =>
    let A := fresh "A" in
    iIntro A; clear A; iIntros
  | |- iHyp (Wand ?P _) _ =>
    let A := fresh "A" in
    iIntro A; iIntros
  | |- iHyp (@Univ _ ?X ?P) _ =>
    let x := fresh "x" in
    intros x; rewrite intro_iHyp; iIntros
  | _ => idtac
  end.

Ltac iAssertP' P H :=
  let name := fresh "my_r" in
  pose (name := @URA.unit (@GRA.to_URA _));
  assert (H: P);
  [subst name|
   change P with (iHyp ⌜P⌝ name) in H;
   on_gwf ltac:(fun GWF => rewrite <- (@URA.unit_id_ _ name eq_refl) in GWF; clearbody name)
  ]
.

Tactic Notation "iAssertP" constr(P) :=
  let H := fresh "H" in
  iAssertP' P H.

Tactic Notation "iAssertP" constr(P) "as" ident(H) :=
  iAssertP' P H.

Ltac _iExploit H :=
  try (match type of H with
       | iHyp (Wand (Pure ?P) _) _ =>
         let H0 := fresh "H" in
         iAssertP P as H0;
         [auto|iSpecialize H H0; _iExploit H]
       | iHyp (Wand ?P _) _ =>
         match goal with
         | H0:iHyp P _ |- _ =>
           iSpecialize H H0; _iExploit H
         end
       end).

Ltac iExploit H :=
  match type of H with
  | iHyp _ _ => _iExploit H
  | _ =>
    let T := fresh "T" in
    hexploit H; intros T; iImpure T; _iExploit T
  end.

Ltac _puregoal H :=
  match H with
  | Wand _ ?Q => _puregoal Q
  | Pure ?P => constr:(Some P: option Prop)
  | _ => constr:(None: option Prop)
  end.

Ltac puregoal H :=
  match type of H with
  | iHyp ?H _ => _puregoal H
  end.

Ltac _iExploitP H :=
  match (puregoal H) with
  | Some ?P => cut P; cycle 1; [_iExploit H; try by apply H|clear H]
  | None => fail
  end.

Ltac iExploitP H :=
  match type of H with
  | iHyp _ _ => _iExploitP H
  | _ =>
    let T := fresh "T" in
    hexploit H; intros T; iImpure T; _iExploitP T
  end.

Ltac iLeft := left; iRefresh.
Ltac iRight := right; iRefresh.


Definition invRA: URA.t := Auth.t (Excl.t unit).
Definition inv_black : (@URA.car invRA) := Auth.black (M:=(Excl.t unit)) (Some tt).
Definition inv_white : (@URA.car invRA) := Auth.white (M:=(Excl.t unit)) (Some tt).

Section AUX.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.

  Definition inv_open: iProp := Own (GRA.embed inv_black).
  Definition inv_closed: iProp := Own (GRA.embed inv_white).

  Lemma inv_closed_unique
    :
      ⌞inv_closed -* inv_closed -* ⌜False⌝⌟
  .
  Proof.
    iIntros.
    unfold inv_closed, inv_white in *.
    iMerge A A0. rewrite <- own_sep in A. rewrite GRA.embed_add in A.
    iOwnWf A. eapply GRA.embed_wf in WF. des. repeat ur in WF. ss.
  Qed.

  Lemma inv_open_unique
    :
      ⌞inv_open -* inv_open -* ⌜False⌝⌟
  .
  Proof.
    iIntros.
    unfold inv_open, inv_black in *.
    iMerge A A0. rewrite <- own_sep in A. rewrite GRA.embed_add in A.
    iOwnWf A. eapply GRA.embed_wf in WF. des. repeat ur in WF. ss.
  Qed.
End AUX.

Ltac inv_clear :=
  exfalso; iRefresh;
  match goal with
  | H0:iHyp inv_closed _ |- _ =>
    iExploitP inv_closed_unique; ss
  | H0:iHyp inv_open _ |- _ =>
    iExploitP inv_open_unique; ss
  end; fail.

Section TEST.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.

  Goal forall mm,
      ⌞inv_open -* ⌜mm⌝ -* (⌜mm⌝ -* inv_open) -* ⌜False⌝⌟
  .
  Proof.
    iIntros. red. red.
    iExploit A1. inv_clear.
  Qed.
End TEST.



Definition knotRA: URA.t := Auth.t (Excl.t (option (nat -> nat))).
Definition knot_full (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.black (M:=(Excl.t _)) (Some f).
Definition knot_frag (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.white (M:=(Excl.t _)) (Some f).

Definition knot_init: (@URA.car knotRA) := knot_frag None.

Section REC.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.

  Definition mrec_spec (f: nat -> nat) (INV: Σ -> Prop): ftspec (list val) val :=
    mk_simple (X:=nat)
              (fun n => (
                   (fun varg o =>
                      (⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n + 1)⌝)
                        ** INV
                   ),
                   (fun vret =>
                      (⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                        ** INV
                   )
              )).

End REC.
