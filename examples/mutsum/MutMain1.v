Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
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

  Definition mainBody: list val -> itree hEs val :=
    fun _ =>
      trigger hAPC;;;
      Ret (Vint 55)
  .

  Definition mainsbtb := [("main", mk_specbody main_spec (cfunN mainBody))].

  Definition SMain: SMod.t := SMod.main (fun varg o => (⌜varg = ([]: list val)↑ ∧ o = ord_top⌝: iProp)%I)
                                        (cfunN mainBody).
  Definition Main: Mod.t := SMod.to_tgt (fun _ => GlobalStb) SMain.

End PROOF.
