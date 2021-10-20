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
Require Import Mem1.

Set Implicit Arguments.


Module AppRA.
Section AppRA.

Variant car: Type :=
| half (usable: bool)
| full
| boom
| unit
.

Let add := fun a0 a1 => match a0, a1 with
                                    | half true, half true => full
                                    | half false, half false => full
                                    | _, unit => a0
                                    | unit, _ => a1
                                    | _, _ => boom
                                    end.
Let wf := fun a => match a with | boom => False | _ => True end.

Program Instance t: URA.t := {
  car := car;
  unit := unit;
  _add := add;
  _wf := wf;
}
.
Next Obligation. subst add wf. i. destruct a, b; ss; des_ifs; ss. Qed.
Next Obligation. subst add wf. i. destruct a, b; ss; des_ifs; ss. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.
Next Obligation. subst add wf. i. unseal "ra". ss. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.

End AppRA.
End AppRA.

Definition Init: AppRA.t := AppRA.half false.
Definition InitX: AppRA.t := AppRA.half false.
Definition Run: AppRA.t := AppRA.half true.
Definition RunX: AppRA.t := AppRA.half true.



Instance mwRA: URA.t := (Z ==> (Excl.t Z))%ra.

Section PROOF.
  Context `{@GRA.inG AppRA.t Σ}.
  Context `{@GRA.inG mwRA Σ}.

  Definition mk_simple_frame {X: Type} (PQ: X -> ((Any.t -> ord -> iProp) * (Any.t -> iProp))): fspec :=
    mk_simple (fun '(FRAME, x) => let '(P, Q) := (PQ x) in
                                  (fun varg ord => FRAME ** P varg ord, fun vret => FRAME ** Q vret))
  .

  Definition init_spec0: fspec :=
    mk_simple (fun (_: unit) => (
                   (fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Init),
                   (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run))).

  Definition run_spec0: fspec :=
    mk_simple (fun (_: unit) => (
                   (fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Run),
                   (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run))).

  Definition main_spec: fspec :=
    mk_simple (fun (_: unit) =>
                 ((fun varg o => OwnM Init),
                  (fun vret => OwnM Run))).

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
    mk_simple (fun f => ((fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Init ** OwnM (f: Z -> option Z)),
                         (fun vret => OwnM Run ** OwnM (add 0%Z 42%Z f)))).

  Definition run_spec1: fspec :=
    mk_simple (fun f => ((fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Run ** OwnM (f: Z -> option Z) ∧ ⌜f 0 = Some 42%Z⌝),
                         (fun vret => OwnM Run ** OwnM f ∧ ⌜f 0 = Some 42%Z⌝))).

  Definition GlobalStb0: gname -> option fspec :=
    to_stb [("init",init_spec0); ("run",run_spec0); ("put",fspec_trivial); ("get",fspec_trivial)].

  Definition GlobalStb1: gname -> option fspec :=
    to_stb [("init",init_spec1); ("run",run_spec1); ("main",main_spec); ("put",put_spec); ("get",get_spec)].

  Context `{@GRA.inG memRA Σ}.

  Definition GlobalStbC: gname -> option fspec :=
    to_stb (List.map (fun x => (x, fspec_trivial)) ["main"; "loop"; "put"; "get"; "init"; "run"; "access"; "update"] ++ MemStb)
  .

End PROOF.
