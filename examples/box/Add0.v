Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.
Set Typeclasses Depth 5.




Section PROOF.
  Context `{@GRA.inG (RA.excl Z) Σ}.

  Definition addF_parg (varg: list val): option unit :=
    match varg with
    | [] => Some tt
    | _ => None
    end
  .

  Definition addF (varg: list val): itree Es val :=
    x <- trigger (Call "get" []);;
    x_plus_one <- vadd x (Vint 1%Z)?;;
    trigger (Call "set" [x_plus_one])
  .

  Definition AddSem: ModSemL.t :=
    {|
      ModSemL.fnsems := [("add", addF) ];
      ModSemL.initial_mrs := [("Add", URA.unit)];
    |}
  .

  Definition Add: Mod.t := {|
    Mod.get_modsem := fun _ => AddSem; (*** TODO: we need proper handling of function pointers ***)
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.
