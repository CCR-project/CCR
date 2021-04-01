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

  Definition getF_parg (varg: list val): option unit :=
    match varg with
    | [] => Some tt
    | _ => None
    end
  .

  Definition getF (varg: Any.t): itree Es Any.t :=
    varg <- varg↓ǃ;;
    mr0 <- trigger (MGet "Box");;
    `x: Z <- trigger (Take _);;
    assume(mr0 = GRA.embed ((inl (Some x)): URA.car (t:=RA.excl Z)));;
    (getF_parg varg)?;;
    Ret (Vint x)↑
  .

  Definition setF_parg (varg: list val): option Z :=
    match varg with
    | [Vint x] => Some x
    | _ => None
    end
  .

  Definition setF (varg: Any.t): itree Es Any.t :=
    varg <- varg↓ǃ;;
    x <- (setF_parg varg)?;;
    MPut "Box" (GRA.embed ((inl (Some x)): URA.car (t:=RA.excl Z)));;
    Ret (Vint 0)↑
  .

  Definition BoxSem: ModSemL.t :=
    {|
      ModSemL.fnsems := [("get", getF) ; ("set", setF) ];
      ModSemL.initial_mrs := [("Box", GRA.embed ((inl (Some 0%Z)): URA.car (t:=RA.excl Z)))];
    |}
  .

  Definition Box: Mod.t := {|
    Mod.get_modsem := fun _ => BoxSem; (*** TODO: we need proper handling of function pointers ***)
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.
