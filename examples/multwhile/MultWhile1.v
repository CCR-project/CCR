Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
Require Import ProofMode.

Set Implicit Arguments.



Section PROOF.
  Context `{Σ: GRA.t}.

  Definition mul_spec: fspec := mk_simple (fun '(a, b) =>
                                             (ord_pure 0,
                                              (fun varg => (⌜varg = (a, b)↑ /\ (0 <= a)%Z⌝: iProp)%I),
                                              (fun vret => (⌜vret = (a * b)%Z↑⌝: iProp)%I))).

  Definition Mulstb: list (string * fspec) := [("mul", mul_spec)].
  Definition Mulsbtb: list (string * fspecbody) := [("mul", mk_specbody mul_spec (fun _ => trigger (Choose _)))].

  Definition SMulSem: SModSem.t := {|
    SModSem.fnsems := Mulsbtb;
    SModSem.mn := "Mul";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SMul: SMod.t := {|
    SMod.get_modsem := fun _ => SMulSem;
    SMod.sk := [("mul", Sk.Gfun)];
  |}
  .

  Definition Mul: Mod.t := (SMod.to_tgt (fun _ => to_stb Mulstb)) SMul.
End PROOF.
