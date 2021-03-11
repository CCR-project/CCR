Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import SimModSem.

Require Import HTactics.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.




Definition ord_le (next cur: ord): Prop :=
  match next, cur with
  | ord_pure next, ord_pure cur => (next <= cur)%nat
  | _, ord_top => True
  | _, _ => False
  end
.

Section PROOF.

  Context `{Σ: GRA.t}.

  Variant fspec_weaker (fsp_src fsp_tgt: fspec): Prop :=
  | fspec_weaker_intro
      mn X_src X_tgt AA_src AA_tgt AR_src AR_tgt
      P_src P_tgt Q_src Q_tgt
      (FSPEC0: fsp_src = @mk _ mn X_src AA_src AR_src P_src Q_src)
      (FSPEC1: fsp_tgt = @mk _ mn X_tgt AA_tgt AR_tgt P_tgt Q_tgt)
  .

Lemma

fspec



  := fun _ => URA.of_RA RA.empty.
