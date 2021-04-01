Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import MutHeader.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  Definition Fsbtb: list (string * fspecbody) := [("f", mk_specbody f_spec (fun _ => trigger (Choose _)))].

  Definition FSem: ModSemL.t := {|
    ModSemL.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt GlobalStb fn body)) Fsbtb;
    ModSemL.initial_mrs := [("F", (ε, tt↑))];
  |}
  .

  Definition F: Mod.t := {|
    Mod.get_modsem := fun _ => FSem;
    Mod.sk := [("f", Sk.Gfun)];
  |}
  .
End PROOF.
