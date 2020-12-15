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



Section PROOF.

  Context `{Σ: GRA.t}.
  (* Context `{@GRA.inG memRA Σ}. *)

  Definition mainBody: list val -> itree (hCallE +' eventE) val := fun _ => trigger (hCall "f" [Vint 10]);; Ret (Vint 55).
  Definition fBody: list val -> itree (hCallE +' eventE) val :=
    fun varg => n <- trigger (Choose _);; trigger (hCall "g" n);; trigger (Choose _)
  .
  Definition FStb: list (fname * funspec) :=
    [("main", mk "F" (X:=unit) top3 top3 mainBody) ;
    ("f", mk "F" (X:=nat) () () fBody)].

  (***
        return f(10);
   ***)
  Definition mainF: list val -> itree Es val :=
    fun _ =>
      trigger (Call "f" [Vint 10])
  .

  (***
    f(n) := if (n == 0) then 0 else (n + g(n-1))
  ***)
  Definition fF: list val -> itree Es val :=
    fun varg =>
      match varg with
      | [Vint n] =>
        if dec n 0
        then Ret (Vint 0)
        else m <- trigger (Call "g" [Vint (n - 1)]);; r <- (vadd (Vint n) m)?;; Ret r
      | _ => triggerUB
      end
  .

  Definition FSem: ModSem.t := {|
    ModSem.fnsems := [("main", mainF) ; ("f", fF)];
    ModSem.initial_mrs := [("F", ε)];
  |}
  .

  Definition F: Mod.t := {|
    Mod.get_modsem := fun _ => FSem;
    Mod.sk := [("f")];
  |}
  .
End PROOF.
