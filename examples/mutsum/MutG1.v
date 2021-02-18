Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import MutHeader.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  Definition gBody: Any.t -> itree (hCallE +' pE +' eventE) Any.t :=
    fun varg => varg' <- trigger (Choose _);; guarantee (ord varg' varg);;
                marg <- trigger (Choose _);; trigger (hCall "f" marg varg');; trigger (Choose _)
  .
  (*** TODO: it would be better if the body can depend on "X", but doing so will mandate generalization of Call.
       related issue: https://github.com/snu-sf/rusc-program-verif/issues/48
   ***)

  Definition GFtb := [("g", gBody)].

  Definition GSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt GlobalStb fn body)) GFtb;
      (* [("main", mainF) ; ("f", fF)]; *)
    ModSem.initial_mrs := [("G", (ε, unit↑))];
  |}
  .

  Definition G: Mod.t := {|
    Mod.get_modsem := fun _ => GSem;
    Mod.sk := [("g", Sk.Gfun)];
  |}
  .
End PROOF.
