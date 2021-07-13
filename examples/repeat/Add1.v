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
Require Import Add0.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Section SKENV.
    Definition succ_spec:    fspec :=
      mk_simple (X:=Z)
                (fun n => (
                     (fun varg o =>
                        (⌜exists o': Ord.t, o = ord_pure o' /\ varg = [Vint n]↑⌝)%I
                     ),
                     (fun vret =>
                        (⌜vret = (Vint (n + 1))↑⌝)%I
                     )
                )).

    Definition add_body: list val -> itree hEs val :=
      fun args =>
        '(n, m) <- (pargs [Tint; Tint] args)?;;
        _ <- assume(intrange_64 m /\ m >= 0)%Z;;;
        Ret (Vint (n + m)%Z)
    .

    Definition AddSbtb: list (gname * kspecbody) :=
      [("succ", mk_kspecbody succ_spec (cfunU succF) (fun _ => triggerNB));
      ("add", ksb_trivial (cfunU add_body))].

    Definition KAddSem: KModSem.t := {|
      KModSem.fnsems := AddSbtb;
      KModSem.mn := "Add";
      KModSem.initial_mr := ε;
      KModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition KAdd: KMod.t := {|
    KMod.get_modsem := fun _ => KAddSem;
    KMod.sk := [("succ", Sk.Gfun); ("add", Sk.Gfun)];
  |}
  .

  Definition Add: Mod.t := (KMod.transl_tgt GlobalStb) KAdd.

End PROOF.
