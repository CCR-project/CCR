Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import ProofMode.

Set Implicit Arguments.



Instance AppRA: URA.t := Excl.t unit.
Definition AppInit: AppRA := (@None unit).
Definition AppRun: AppRA := Some tt.


Instance mwRA: URA.t := (Z ==> (Excl.t Z))%ra.

Section PROOF.
  Context `{@GRA.inG AppRA Σ}.
  Context `{@GRA.inG mwRA Σ}.

  Definition init_spec0: fspec :=
    mk_simple (fun (_: unit) => ((fun varg o => (OwnM AppInit)), (fun vret => (OwnM AppRun)))).

  Definition run_spec0: fspec :=
    mk_simple (fun (_: unit) => ((fun varg o => (OwnM AppRun)), (fun vret => (OwnM AppRun)))).

  Definition main_spec: fspec :=
    mk_simple (fun (_: unit) =>
                 ((fun varg o => OwnM AppInit),
                  (fun vret => OwnM AppRun))).

  Definition put_spec: fspec :=
    mk_simple (fun '(f, k, v) =>
                 ((fun varg o => ⌜varg = [Vint k; Vint v]↑ ∧ intrange_64 k ∧ intrange_64 v⌝ ** OwnM (f: Z -> option Z)),
                  (fun vret => OwnM (add k v f))))
  .

  Definition get_spec: fspec :=
    mk_simple (fun '(f, k, v) =>
                 ((fun varg o => ⌜varg = [Vint k]↑ ∧ intrange_64 k ∧ f k = Some v⌝ ** OwnM (f: Z -> option Z)),
                  (fun vret => ⌜vret = (Vint v)↑⌝ ** OwnM f)))
  .

  Definition init_spec1: fspec :=
    mk_simple (fun f => ((fun varg o => OwnM AppInit ** OwnM f),
                         (fun vret => OwnM AppRun ** OwnM f ∧ ⌜f 0 = Some 42%Z⌝))).

  Definition run_spec1: fspec :=
    mk_simple (fun f => ((fun varg o => OwnM AppRun ** OwnM f ∧ ⌜f 0 = Some 42%Z⌝),
                         (fun vret => OwnM AppRun ** OwnM f ∧ ⌜f 0 = Some 42%Z⌝))).

  Definition GlobalStb0: gname -> option fspec :=
    to_stb [("init",init_spec0); ("run",run_spec0)].

  Definition GlobalStb1: gname -> option fspec :=
    to_stb [("init",init_spec1); ("run",run_spec1); ("main",main_spec); ("put",put_spec); ("get",get_spec)].

End PROOF.
