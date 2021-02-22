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

  Definition mainBody: list val -> itree (hCallE +' pE +' eventE) val := fun _ => trigger (hCall true "f" [Vint 10]↑);; Ret (Vint 55).
  Definition fBody: list val -> itree (hCallE +' pE +' eventE) val :=
    fun varg => varg' <- trigger (Choose _);; guarantee (_ord varg' varg);;
                trigger (hCall true "g" varg'↑);; trigger (Choose _)
  .
  (*** TODO: it would be better if the body can depend on "X", but doing so will mandate generalization of Call.
       related issue: https://github.com/snu-sf/rusc-program-verif/issues/48
   ***)

  (*** TODO: unify convention; mainBody -> main_body? ***)
  Definition Fsbtb: list (string * fspecbody) := [("main", mk_specbody main_spec mainBody); ("f", mk_specbody f_spec fBody)].

  Definition FSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt GlobalStb fn body)) Fsbtb;
      (* [("main", mainF) ; ("f", fF)]; *)
    ModSem.initial_mrs := [("F", (ε, unit↑))];
  |}
  .

  Definition F: Mod.t := {|
    Mod.get_modsem := fun _ => FSem;
    Mod.sk := [("f", Sk.Gfun)];
  |}
  .
End PROOF.
