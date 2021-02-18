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

  Definition mainBody: Any.t -> itree (hCallE +' pE +' eventE) Any.t := fun _ => marg <- trigger (Choose _);; trigger (hCall "f" marg [Vint 10]↑);; Ret (Vint 55)↑.
  Definition fBody: Any.t -> itree (hCallE +' pE +' eventE) Any.t :=
    fun varg => varg' <- trigger (Choose _);; guarantee (ord varg' varg);;
                marg <- trigger (Choose _);; trigger (hCall "g" marg varg');; trigger (Choose _)
  .
  (*** TODO: it would be better if the body can depend on "X", but doing so will mandate generalization of Call.
       related issue: https://github.com/snu-sf/rusc-program-verif/issues/48
   ***)

  Definition FFtb := [("main", mainBody) ; ("f", fBody)].

  Definition FSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt GlobalStb fn body)) FFtb;
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
