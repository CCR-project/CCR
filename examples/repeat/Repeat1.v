Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef OpenDef.
Require Import ProofMode.
Require Import STB.
Require Import Repeat0.

Set Implicit Arguments.



Section PROOF.

  Fixpoint repeat_fun A (f: A -> A) (n: nat) (a: A): A :=
    match n with
    | 0 => a
    | S n' => repeat_fun f n' (f a)
    end.

  Context `{Σ: GRA.t}.

  Variable FunStb: Sk.t -> gname -> option fspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Section SKENV.
    Variable sk: Sk.t.

    Definition repeat_spec:    fspec :=
      mk_simple (X:=nat * nat * Z * (Z -> Z))
                (fun '(f, n, x, f_spec) => (
                     (ord_pure (Ord.omega + n)%ord),
                     (fun varg =>
                        (⌜varg = [Vptr f 0; Vint (Z.of_nat n); Vint x]↑ /\ (intrange_64 n)
                         /\ fb_has_spec
                              (Sk.load_skenv sk) (FunStb sk) f
                              (mk_simple
                                 (X:=Z)
                                 (fun x =>
                                    ((ord_pure Ord.omega),
                                     (fun varg => ⌜varg = [Vint x]↑⌝),
                                     (fun vret => ⌜vret = (Vint (f_spec x))↑⌝))))⌝: iProp)%I
                     ),
                     (fun vret =>
                        (⌜vret = (Vint (repeat_fun f_spec n x))↑⌝)%I
                     )
                )).

    Definition RepeatSbtb: list (gname * kspecbody) :=
      [("repeat", mk_kspecbody repeat_spec (fun _ => triggerUB) (fun _ => triggerNB))].

    Definition KRepeatSem: KModSem.t := {|
      KModSem.fnsems := RepeatSbtb;
      KModSem.mn := "Repeat";
      KModSem.initial_mr := ε;
      KModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition KRepeat: KMod.t := {|
    KMod.get_modsem := KRepeatSem;
    KMod.sk := [("repeat", Sk.Gfun)];
  |}
  .

  Definition Repeat: Mod.t := (KMod.transl_tgt GlobalStb) KRepeat.

End PROOF.
