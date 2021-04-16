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

  Variable cmpspecs: list (gname * (Z -> Z -> Z)).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Section SKENV.
    Variable skenv: SkEnv.t.

    Definition wrap_spec:    fspec := mk_simple "Wrap" (X:=Z*Z*(Z -> Z -> Z))
                                                (fun '(n0, n1, f) => (
                                                     (fun varg o => ⌜exists fn blk, varg = [Vint n0; Vint n1; Vptr blk 0]↑ /\ o = ord_pure 1 /\ skenv.(SkEnv.blk2id) blk = Some fn /\ List.find (fun '(_fn, _) => dec fn _fn) cmpspecs = Some (fn, f)⌝), 
                                                     (fun vret => ⌜vret = (Vint (f n0 n1))↑⌝)
                                                )).

    Definition Wrapstb: list (gname * fspec) := [("wrap", wrap_spec)].

    Definition Wrapsbtb: list (gname * fspecbody) := [("wrap", mk_specbody wrap_spec (fun _ => trigger (Choose _)))].

    Definition WrapSem: ModSem.t := {|
      ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt (GlobalStb skenv) fn body)) Wrapsbtb;
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

(* Definition cmpspecs: gname -> option (Z -> Z -> Z) := *)
(*   fun fn => option_map snd (List.find (fun '(str, _) => eqb str fn) [("compare", mycmp)]). *)
