Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem.
Require Import Behavior.
Require Import Relation_Definitions.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.



Section WTY.
  Context `{Σ: GRA.t}.
  Variable ms: ModSem.t.

  Theorem soundness
    :
      Beh.improves (Beh.of_program (ModSem.interp_no_forge ms))
                   (Beh.of_program (ModSem.interp ms))
  .
  Proof.
    admit "TODO".
  Qed.

End WTY.
