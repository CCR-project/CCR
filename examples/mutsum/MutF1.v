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


Fixpoint sum (n: nat): nat :=
  match n with
  | O => O
  | S m => n + sum m
  end
.
Compute (sum 10).

Section PROOF.

  Context `{Σ: GRA.t}.
  (* Context `{@GRA.inG memRA Σ}. *)

  Definition mainBody: list val -> itree (hCallE +' eventE) val := fun _ => trigger (hCall "f" [Vint 10]);; Ret (Vint 55).
  Definition fBody: list val -> itree (hCallE +' eventE) val :=
    fun varg => n <- trigger (Choose _);; trigger (hCall "g" n);; trigger (Choose _)
  .
  (*** TODO: it would be better if the body can depend on "X", but doing so will mandate generalization of Call.
       related issue: https://github.com/snu-sf/rusc-program-verif/issues/48
   ***)
  Definition FSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fs, body) => (fn, fun_to_tgt GlobalStb fs body)) FFtb;
      (* [("main", mainF) ; ("f", fF)]; *)
    ModSem.initial_mrs := [("F", ε)];
  |}
  .

  Definition F: Mod.t := {|
    Mod.get_modsem := fun _ => FSem;
    Mod.sk := [("f")];
  |}
  .
End PROOF.
