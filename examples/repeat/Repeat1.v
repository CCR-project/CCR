Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.

Set Implicit Arguments.



Section PROOF.

  Fixpoint repeat_fun A (f: A -> A) (n: nat) (a: A): A :=
    match n with
    | 0 => a
    | S n' => repeat_fun f n' (f a)
    end.

  Context `{Σ: GRA.t}.

  Variable FunStb: SkEnv.t -> gname -> option fspec.
  Variable GlobalStb: SkEnv.t -> gname -> option fspec.

  Section SKENV.
    Variable skenv: SkEnv.t.

    Definition repeat_spec:    fspec :=
      mk_simple (X:=nat * nat * Z * (Z -> Z))
                (fun '(f, n, x, f_spec) => (
                     (fun varg o =>
                        (⌜o = ord_pure n /\ varg = [Vptr f 0; Vint (Z.of_nat n); Vint x]↑ /\ (intrange_64 n)
                         /\ fb_has_spec
                              skenv (FunStb skenv) f
                              (mk_simple
                                 (X:=Z)
                                 (fun x =>
                                    ((fun varg o =>
                                        ⌜o = ord_pure 0 /\ varg = [Vint x]↑⌝),
                                     (fun vret => ⌜vret = (Vint (f_spec x))↑⌝))))⌝: iProp)%I
                     ),
                     (fun vret =>
                        (⌜vret = (Vint (repeat_fun f_spec n x))↑⌝)%I
                     )
                )).

    Definition RepeatSbtb: list (gname * fspecbody) :=[("repeat", mk_specbody repeat_spec (fun _ => trigger (Choose _)))].

    Definition SRepeatSem: SModSem.t := {|
      SModSem.fnsems := RepeatSbtb;
      SModSem.mn := "Repeat";
      SModSem.initial_mr := ε;
      SModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition SRepeat: SMod.t := {|
    SMod.get_modsem := SRepeatSem;
    SMod.sk := [("repeat", Sk.Gfun)];
  |}
  .

  Definition Repeat: Mod.t := (SMod.to_tgt GlobalStb) SRepeat.

End PROOF.
