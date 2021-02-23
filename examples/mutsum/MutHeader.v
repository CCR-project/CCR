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

  Definition main_spec: fspec := mk_simple "Main" (X:=unit) (fun _ _ _ o => o = ord_top) top3.
  Definition f_spec:    fspec := mk_simple "F" (X:=nat) (fun n varg _ o => varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n) (fun n vret _ => vret = (Vint (Z.of_nat (sum n)))↑).
  Definition g_spec:    fspec := mk_simple "G" (X:=nat) (fun n varg _ o => varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n) (fun n vret _ => vret = (Vint (Z.of_nat (sum n)))↑).
  Definition GlobalStb: list (gname * fspec) := [("main", main_spec); ("f", f_spec); ("g", g_spec)].

End PROOF.
