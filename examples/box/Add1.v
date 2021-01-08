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
Set Typeclasses Depth 4.




Section PROOF.
  Context `{@GRA.inG boxRA Σ}.
  (* Let GURA: URA.t := GRA.to_URA Σ. *)
  (* Local Existing Instance GURA. *)

  Definition addBody (varg: list val): itree (hCallE +' eventE) val :=
    x <- trigger (hCall "get" []);;
    x_plus_one <- vadd x (Vint 1%Z)?;;
    trigger (hCall "set" [x_plus_one])
  .

  Definition AddFtb: list (fname * (list val -> itree (hCallE +' eventE) val)) :=
    zip pair ["add"] [addBody]
  .

  Definition AddSem: ModSem.t :=
    {|
      ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt (BoxStb++AddStb) fn body)) AddFtb;
      ModSem.initial_mrs := [("Add", URA.unit)];
    |}
  .

  Definition Add: Mod.t := {|
    Mod.get_modsem := fun _ => AddSem; (*** TODO: we need proper handling of function pointers ***)
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.
