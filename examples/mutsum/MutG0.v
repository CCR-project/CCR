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

  (***
    g(n) := if (n == 0) then 0 else (n + f(n-1))
  ***)
  Definition gF: Any.t -> itree Es Any.t :=
    fun varg =>
      varg <- varg↓ǃ;;
      match varg with
      | [Vint n] =>
        if dec n 0%Z
        then Ret (Vint 0)↑
        else m <- trigger (Call "f" [Vint (n - 1)]↑);; m <- m↓ǃ;; r <- (vadd (Vint n) m)?;; Ret r↑
      | _ => triggerUB
      end
  .

  Definition GSem: ModSem.t := {|
    ModSem.fnsems := [("g", gF)];
    ModSem.initial_mrs := [("G", (ε, unit↑))];
  |}
  .

  Definition G: Mod.t := {|
    Mod.get_modsem := fun _ => GSem;
    Mod.sk := [("g")];
  |}
  .
End PROOF.
