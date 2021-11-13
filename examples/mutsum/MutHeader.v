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


Fixpoint sum (n: nat): nat :=
  match n with
  | O => O
  | S m => n + sum m
  end
.
Compute (sum 10). (* 55 *)


Definition mut_max: nat := 1000%nat.

Lemma mut_max_intrange x
      (LT: x < mut_max)
  :
    intrange_64 x.
Proof.
  unfold mut_max in *. unfold_intrange_64. rewrite two_power_nat_S.
  replace (2 * two_power_nat 63)%Z with ((two_power_nat 63) * 2)%Z.
  2:{ rewrite Z.mul_comm. lia. }
  unfold two_power_nat. ss.
  unfold sumbool_to_bool. des_ifs; try lia.
  all: rewrite Z.div_mul in *; try lia.
Qed.

Lemma mut_max_intrange_sub1 x
      (LT: x < mut_max)
  :
    intrange_64 (x - 1).
Proof.
  unfold mut_max in *. unfold_intrange_64. rewrite two_power_nat_S.
  replace (2 * two_power_nat 63)%Z with ((two_power_nat 63) * 2)%Z.
  2:{ rewrite Z.mul_comm. lia. }
  unfold two_power_nat. ss.
  unfold sumbool_to_bool. des_ifs; try lia.
  all: rewrite Z.div_mul in *; try lia.
Qed.

Lemma mut_max_sum_intrange x
      (LT: x < mut_max)
  :
    intrange_64 (sum x).
Proof.
  cut (sum x <= mut_max * mut_max)%Z.
  { unfold mut_max.
    generalize (sum x). clear LT. intros n LT.
    unfold_intrange_64. rewrite two_power_nat_S.
    replace (2 * two_power_nat 63)%Z with ((two_power_nat 63) * 2)%Z.
    2:{ rewrite Z.mul_comm. lia. }
    unfold two_power_nat. ss.
    unfold sumbool_to_bool. des_ifs; try lia.
    all: rewrite Z.div_mul in *; try lia.
  }
  cut (sum x <= x * x).
  { i. rewrite <- Nat2Z.inj_mul. apply inj_le.
    etrans; et. etrans.
    { eapply mult_le_compat_r. instantiate (1:=mut_max). lia. }
    { eapply mult_le_compat_l. lia. }
  }
  induction x; ss. lia.
Qed.

Section PROOF.

  Context `{Σ: GRA.t}.

  Definition main_spec: fspec :=
    mk_simple (fun (_: unit) => (ord_top, (fun varg => (⌜varg = ([]: list val)↑⌝: iProp)%I),
                                 fun _ => (True: iProp)%I)).
  Definition f_spec:    fspec := mk_simple (fun (n: nat) =>
                                              (ord_pure n,
                                               (fun varg => (⌜varg = [Vint (Z.of_nat n)]↑ /\ n < mut_max⌝: iProp)%I),
                                               (fun vret => (⌜vret = (Vint (Z.of_nat (sum n)))↑⌝: iProp)%I))).
  Definition g_spec:    fspec := mk_simple (fun (n: nat) =>
                                              (ord_pure n,
                                               (fun varg => (⌜varg = [Vint (Z.of_nat n)]↑ /\ n < mut_max⌝: iProp)%I),
                                               (fun vret => (⌜vret = (Vint (Z.of_nat (sum n)))↑⌝: iProp)%I))).
  Definition GlobalStb: gname -> option fspec := to_stb [("main", main_spec); ("f", f_spec); ("g", g_spec)].

End PROOF.
