Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import CompareHeader.
Require Import Logic.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Section SKENV.
    Variable skenv: SkEnv.t.

    Definition main_spec: fspec := mk_simple "Main" (X:=unit)
                                             (fun _ => (
                                                  (fun _ o => ⌜o = ord_top⌝),
                                                  top2
                                             )).

    Definition compare_spec:    fspec := compare_gen mycmp "Main".

    Definition MainCmpsStb: list (gname * fspec) := [("compare", compare_spec)].

    Definition MainStb: list (gname * fspec) := [("main", main_spec); ("compare", compare_spec)].

    Definition MainSbtb: list (gname * fspecbody) := [("main", mk_specbody main_spec (fun _ => APC;; trigger (Choose _))); ("compare", mk_specbody compare_spec (fun _ => trigger (Choose _)))].

    Definition MainSem: ModSem.t := {|
      ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt (GlobalStb skenv) fn body)) MainSbtb;
      ModSem.mn := "Main";
      ModSem.initial_mr := ε;
      ModSem.initial_st := tt↑;
                                   |}
    .
  End SKENV.

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun skenv => MainSem skenv;
    Mod.sk := [("compare", Sk.Gfun)];
  |}
  .

End PROOF.
