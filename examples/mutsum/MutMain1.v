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

  Definition mainBody: list val -> itree (hCallE +' pE +' eventE) val :=
    fun _ =>
      trigger (hCall true "f" [Vint 10]↑);;
      Ret (Vint 55)
  .

  Definition mainsbtb := [("main", mk_specbody main_spec mainBody)].

  Definition mainSem: ModSemL.t := {|
    ModSemL.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt GlobalStb fn body)) mainsbtb;
    ModSemL.initial_mrs := [("Main", (ε, tt↑))];
  |}
  .

  Definition main: Mod.t := {|
    Mod.get_modsem := fun _ => mainSem;
    Mod.sk := [("Main", Sk.Gfun)];
  |}
  .
End PROOF.
