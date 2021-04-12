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

  Definition addBody (varg: list val): itree (hCallE +' eventE) val :=
    trigger (hCall "get" []);;
    varg <- trigger (Choose _);;
    trigger (hCall "set" [varg])
  .

  Definition AddFtb: list (gname * (list val -> itree (hCallE +' eventE) val)) :=
    zip pair ["add"] [addBody]
  .

  Definition AddSem: ModSemL.t :=
    {|
      ModSemL.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt (BoxStb++AddStb) fn body)) AddFtb;
      ModSemL.initial_mrs := [("Add", URA.unit)];
    |}
  .

  Definition Add: Mod.t := {|
    Mod.get_modsem := fun _ => AddSem; (*** TODO: we need proper handling of function pointers ***)
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.
