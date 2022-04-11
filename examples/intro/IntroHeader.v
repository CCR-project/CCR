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



Definition max: nat := 1000%nat.

Lemma max_intrange x
      (LT: x < max)
  :
    intrange_64 x.
Proof.
  unfold max in *. unfold_intrange_64. rewrite two_power_nat_S.
  replace (2 * two_power_nat 63)%Z with ((two_power_nat 63) * 2)%Z.
  2:{ rewrite Z.mul_comm. lia. }
  unfold two_power_nat. ss.
  unfold sumbool_to_bool. des_ifs; try lia.
  all: rewrite Z.div_mul in *; try lia.
Qed.

Global Opaque Z.mul Nat.mul.



Definition Ncall X Y P Q (f: string) (x: X): itree Es Y :=
  `b: bool <- trigger (Choose bool);;
  if b
  then guarantee(P);;; r <- ccallU f x;; assume (Q r);;; Ret r
  else r <- trigger (Choose _);; guarantee (Q r);;; Ret r
.

Definition f_measure (n: nat): ord := ord_pure (2*n).
Definition g_measure (n: nat): ord := ord_pure (2*n - 1).

Module Plain.
Section PROOF.

  Context `{Σ: GRA.t}.

  Definition f_spec: fspec :=
    mk_simple (fun (n: nat) =>
                 (f_measure n,
                  (fun varg => (⌜varg = [Vint (Z.of_nat n)]↑ /\ n < max⌝: iProp)%I),
                  (fun vret => (⌜vret = (Vint (Z.of_nat (5 * n)))↑⌝: iProp)%I))).
  Definition g_spec: fspec :=
    mk_simple (fun (n: nat) =>
                 (g_measure n,
                  (fun varg => (⌜varg = [Vint (Z.of_nat n)]↑ /\ 1 <= n < max⌝: iProp)%I),
                  (fun vret => (⌜vret = (Vint (Z.of_nat (5 * n - 2)))↑⌝: iProp)%I))).
  Definition GlobalStb: gname -> option fspec := to_stb [("f", f_spec); ("g", g_spec)].

End PROOF.
End Plain.




(*** RA for the intro example ***)
Module IRA.
Section IRA.

Variant car: Type :=
| module (usable: bool)
| client (usable: bool)
| full
| boom
| unit
.

Let add := fun a0 a1 => match a0, a1 with
                                    | module true, client true => full
                                    | module false, client false => full
                                    | module true, client false => full
                                    | client true, module true => full
                                    | client false, module false => full
                                    | client false, module true => full
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
  core := fun _ => unit;
}
.
Next Obligation. subst add wf. i. destruct a, b; ss; des_ifs; ss. Qed.
Next Obligation. subst add wf. i. destruct a, b; ss; des_ifs; ss. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.
Next Obligation. subst add wf. i. unseal "ra". ss. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.
Next Obligation.
  i. exists unit. subst add. unseal "ra". des_ifs.
Qed.

End IRA.
End IRA.



Module Sep.
Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG IRA.t Σ}.

  Definition f_spec: fspec :=
    mk_simple (fun (n: nat) =>
                 (f_measure n,
                  (fun varg => (⌜varg = [Vint (Z.of_nat n)]↑ /\ n < max⌝
                                  ** OwnM (IRA.client true: IRA.t))),
                  (fun vret => (⌜vret = (Vint (Z.of_nat (5 * n)))↑⌝
                                 ** OwnM (IRA.client false: IRA.t))))).
  Definition g_spec: fspec :=
    mk_simple (fun (n: nat) =>
                 (g_measure n,
                  (fun varg => (⌜varg = [Vint (Z.of_nat n)]↑ /\ 1 <= n < max⌝
                                   ** OwnM (IRA.client true: IRA.t))),
                  (fun vret => (⌜vret = (Vint (Z.of_nat (5 * n - 2)))↑⌝
                                   ** OwnM (IRA.client false: IRA.t))))).
  Definition GlobalStb: gname -> option fspec := to_stb [("f", f_spec); ("g", g_spec)].

End PROOF.
End Sep.
