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

  Context `{Σ: GRA.t}.

  Variable FunStb: SkEnv.t -> gname -> option fspec.
  Variable GlobalStb: SkEnv.t -> gname -> option fspec.

  Section SKENV.
    Variable skenv: SkEnv.t.

    Definition succ_spec:    fspec :=
      mk_simple (X:=Z)
                (fun n => (
                     (fun varg o =>
                        (⌜o = ord_pure 0 /\ varg = [Vint n]↑⌝)%I
                     ),
                     (fun vret =>
                        (⌜vret = (Vint (n + 1))↑⌝)%I
                     )
                )).

    Definition add_spec:    fspec :=
      mk_simple (X:=Z * nat)
                (fun '(n, m) => (
                     (fun varg o =>
                        (⌜o = ord_pure (m + 1)%nat /\ varg = [Vint n; Vint (Z.of_nat m)]↑ /\ intrange_64 m⌝)%I
                     ),
                     (fun vret =>
                        (⌜vret = (Vint (n + m))↑⌝)%I
                     )
                )).

    Definition AddSbtb: list (gname * fspecbody) :=[("succ", mk_specbody succ_spec (fun _ => trigger (Choose _))); ("add", mk_specbody add_spec (fun _ => trigger (Choose _)))].

    Definition SAddSem: SModSem.t := {|
      SModSem.fnsems := AddSbtb;
      SModSem.mn := "Add";
      SModSem.initial_mr := ε;
      SModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition SAdd: SMod.t := {|
    SMod.get_modsem := fun _ => SAddSem;
    SMod.sk := [("succ", Sk.Gfun); ("add", Sk.Gfun)];
  |}
  .

  Definition Add: Mod.t := (SMod.to_tgt GlobalStb) SAdd.

End PROOF.
