Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  (***
    main() := return f(10)
  ***)
  Definition mainF: mname * Any.t -> itree Es Any.t :=
    fun '(_, varg) =>
      r <- trigger (Call "f" [Vint 10]↑);;
      Ret r.

  Definition MainSem: ModSem.t := {|
    ModSem.fnsems := [("main", mainF)];
    ModSem.mn := "Main";
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    (* Mod.sk := [("Main", Sk.Gfun)]; *)
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
