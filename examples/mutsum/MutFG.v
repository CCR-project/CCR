Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import MutHeader.
Require Import MutF1 MutG1.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  Definition FG1: Mod.t := Mod.add F G.

  Definition FG2: Mod.t := {|
    Mod.get_modsem := fun _ => {|
        ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_src body)) (FFtb ++ GFtb);
        ModSem.initial_mrs := [];
      |};
    Mod.sk := Sk.unit;
  |}
  .

  Theorem correct: Beh.of_program (Mod.interp FG1) <1= Beh.of_program (Mod.interp FG2).
  Proof.
    ii.
    eapply adequacy_type with (ftb:=FFtb++GFtb) in PR. cbn in *.
    rp; try apply PR; cycle 1.
    { refl. }
    clear PR. f_equal.
  Qed.

End PROOF.
