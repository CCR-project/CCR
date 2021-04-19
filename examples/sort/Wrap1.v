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

  Variable CmpsStb: SkEnv.t -> list (gname * fspec).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Section SKENV.
    Variable skenv: SkEnv.t.

    (* TODO: define (myfind: list (string * A) -> A -> option A) and use it *)
    Definition wrap_spec:    fspec := mk_simple "Wrap" (X:=Z*Z*(Z -> Z -> Z))
                                                (fun '(n0, n1, f) => (
                                                     (fun varg o => ⌜exists fn blk, varg = [Vint n0; Vint n1; Vptr blk 0]↑ /\ o = ord_pure 1 /\ skenv.(SkEnv.blk2id) blk = Some fn /\ List.find (fun '(_fn, _) => dec fn _fn) (CmpsStb skenv) = Some (fn, compare_gen f fn)⌝),
                                                     (fun vret => ⌜vret = (Vint (f n0 n1))↑⌝)
                                                )).

    Definition WrapStb: list (gname * fspec) := [("wrap", wrap_spec)].

    Definition WrapSbtb: list (gname * fspecbody) := [("wrap", mk_specbody wrap_spec (fun _ => trigger (Choose _)))].

    Definition WrapSem: ModSem.t := {|
      ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt (GlobalStb skenv) fn body)) WrapSbtb;
      ModSem.mn := "Wrap";
      ModSem.initial_mr := ε;
      ModSem.initial_st := tt↑;
                                   |}
    .
  End SKENV.

  Definition Wrap: Mod.t := {|
    Mod.get_modsem := fun skenv => WrapSem skenv;
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.
