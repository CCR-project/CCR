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


Fixpoint sum (n: nat): nat :=
  match n with
  | O => O
  | S m => n + sum m
  end
.
Compute (sum 10).




Section PROOF.
  Context {Σ: GRA.t}.
  (*** TODO: move to proper place, together with "mk_simple" ***)
  (*** TODO: rename sb into spb ***)
  (*** TODO: remove redundancy with Hoareproof0.v ***)
  Definition mk_simple (mn: string) {X: Type} (P: X -> Any.t -> Σ -> ord -> Prop) (Q: X -> Any.t -> Σ -> Prop): fspec :=
    @mk _ mn X (list val) (val) (fun x y a r o => P x a r o /\ y↑ = a) (fun x z a r => Q x a r /\ z↑ = a)
  .
  Definition mk_sb_simple (mn: string) {X: Type} (P: X -> Any.t -> Σ -> ord -> Prop) (Q: X -> Any.t -> Σ -> Prop)
             (body: list val -> itree (hCallE +' pE +' eventE) val): fspecbody := mk_specbody (mk_simple mn P Q) body.

End PROOF.




Section PROOF.

  Context `{Σ: GRA.t}.

  Definition main_spec: fspec := mk_simple "F" (X:=unit) (fun _ _ _ o => o = ord_top) top3.
  Definition f_spec:    fspec := mk_simple "F" (X:=nat) (fun n varg _ o => varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n) (fun n vret _ => vret = (Vint (Z.of_nat (sum n)))↑).
  Definition g_spec:    fspec := mk_simple "G" (X:=nat) (fun n varg _ o => varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n) (fun n vret _ => vret = (Vint (Z.of_nat (sum n)))↑).
  Definition GlobalStb: list (gname * fspec) := [("main", main_spec); ("f", f_spec); ("g", g_spec)].

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
