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
Set Typeclasses Depth 5.




Section PROOF.
  Context `{@GRA.inG boxRA Σ}.
  (* Let GURA: URA.t := GRA.to_URA Σ. *)
  (* Local Existing Instance GURA. *)

  Definition BoxFtb: list (fname * (list val -> itree (hCallE +' eventE) val)) :=
    zip pair ["get"; "set"] (List.repeat (fun _ => trigger (Choose _)) 2)
  .

  Definition BoxSem: ModSem.t :=
    {|
      ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt BoxStb fn body)) BoxFtb;
      ModSem.initial_mrs := [("Box", library 0%Z)];
    |}
  .

  Definition Box: Mod.t := {|
    Mod.get_modsem := fun _ => BoxSem; (*** TODO: we need proper handling of function pointers ***)
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.
