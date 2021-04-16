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
Require Import Logic.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  Definition mycmp (n0 n1: Z): Z :=
    if (Z_le_gt_dec n0 n1)
    then 0
    else 1.

  Variable cmpspecs: gname -> option (Z -> Z -> Z).

  Section SKENV.
    Variable skenv: SkEnv.t.

    Definition main_spec: fspec := mk_simple "Main" (X:=unit) 
                                             (fun _ => (
                                                  (fun _ o => ⌜o = ord_top⌝),
                                                  top2
                                             )).

    Definition compare_spec:    fspec := mk_simple "Main" (X:=Z*Z)
                                                   (fun '(n0, n1) => (
                                                        (fun varg o => ⌜varg = [Vint n0; Vint n1]↑ /\ o = ord_pure 1⌝), 
                                                        (fun vret => ⌜vret = (Vint (mycmp n0 n1))↑⌝)
                                                   )).

    Definition wrap_spec:    fspec := mk_simple "Main" (X:=Z*Z*(Z -> Z -> Z))
                                                (fun '(n0, n1, f) => (
                                                     (fun varg o => ⌜exists fn blk, varg = [Vint n0; Vint n1; Vptr blk 0]↑ /\ o = ord_pure 1 /\ skenv.(SkEnv.blk2id) blk = Some fn /\ cmpspecs fn = Some f⌝), 
                                                     (fun vret => ⌜vret = (Vint (f n0 n1))↑⌝)
                                                )).

    Definition Mainsbtb: list (string * fspecbody) := [("main", mk_specbody main_spec (fun _ => APC;; trigger (Choose _))); ("compare", mk_specbody compare_spec (fun _ => trigger (Choose _))); ("wrap", mk_specbody wrap_spec (fun _ => trigger (Choose _)))].

    Definition GlobalStb: list (gname * fspec) := [("main", main_spec); ("compare", compare_spec); ("wrap", wrap_spec)].

    Definition MainSem: ModSem.t := {|
      ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt GlobalStb fn body)) Mainsbtb;
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

Definition cmpspecs: gname -> option (Z -> Z -> Z) :=
  fun fn => option_map snd (List.find (fun '(str, _) => eqb str fn) [("compare", mycmp)]).
