Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.


Fixpoint sum (n: nat): nat :=
  match n with
  | O => O
  | S m => n + sum m
  end
.
Compute (sum 10).

Section PROOF.

  Context `{Σ: GRA.t}.

  Definition GlobalStb: list (gname * fspec) := [
    ("main", mk "F" (X:=unit) top3 top3) ;
    ("f", mk "F" (X:=nat) (fun n varg _ => varg = [Vint (Z.of_nat n)]↑) (fun n vret _ => vret = (Vint (Z.of_nat (sum n)))↑)) ;
    ("g", mk "F" (X:=nat) (fun n varg _ => varg = [Vint (Z.of_nat n)]↑) (fun n vret _ => vret = (Vint (Z.of_nat (sum n)))↑))
  ].

End PROOF.


Definition _ord: list val -> list val -> Prop := fun vs0 vs1 => exists n, vs0 = [Vint (Z.of_nat n)] /\ vs1 = [Vint (Z.of_nat (S n))].

Theorem _ord_well_founded: well_founded _ord.
Proof.
  ii. destruct a.
  { econs; ii. inv H; ss. des; clarify. }
  destruct a; cycle 1.
  { econs; ii. inv H; ss. des; clarify. }
  destruct v; ss; cycle 1.
  { econs; ii. inv H; ss. des; clarify. }
  { econs; ii. inv H; ss. des; clarify. }
  pattern n. eapply well_founded_ind.
  { eapply Z.lt_wf with (z:=0%Z). }
  i. ss. econs. ii. inv H0; ss. des; clarify. eapply H. lia.
Qed.

Definition ord: Any.t -> Any.t -> Prop := fun a0 a1 => exists vs0 vs1, a0 = vs0↑ /\ a1 = vs1↑ /\ _ord vs0 vs1.

Theorem ord_well_founded: well_founded ord.
Proof.
  admit "ez - import wf-map from CompCertM".
Qed.
