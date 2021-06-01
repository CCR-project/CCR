Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Logic.
Require Import MutHeader.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  Definition mainBody: list val -> itree (hCallE +' pE +' eventE) val :=
    fun _ =>
      trigger (hCall true "f" [Vint 10]↑);;;
      Ret (Vint 55)
  .

  Definition mainsbtb := [("main", mk_specbody main_spec (cfun mainBody))].

  Definition SMain: SMod.t := SMod.main (fun _ o => (⌜o = ord_top⌝: iProp)%I) (cfun mainBody).
  Definition Main: Mod.t := SMod.to_tgt (fun _ => GlobalStb) SMain.

End PROOF.
