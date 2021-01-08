Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import BoxHeader.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG boxRA Σ}.

  Definition mainBody: list val -> itree (hCallE +' eventE) val :=
    fun _ =>
      trigger (hCall "set" [Vint 10]);;
      r <- trigger (hCall "get" []);;
      Ret (Vint 10)
  .

  Definition MainFtb := zip pair [("main")] [mainBody].

  Definition MainSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt (MainStb ++ BoxStb) fn body)) MainFtb;
    ModSem.initial_mrs := [("Main", client 0%Z)];
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := List.map fst MainStb;
  |}
  .

End PROOF.
