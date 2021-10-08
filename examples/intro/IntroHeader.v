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

Definition Ncall X Y P Q (f: string) (x: X): itree Es Y :=
  guarantee(P);;;
  `b: bool <- trigger (Choose bool);;
  r <- (if b then ccallU f x else trigger (Choose _));;
  assume(Q r);;;
  Ret r
.

Section PROOF.

  Context `{Σ: GRA.t}.

  Definition f_spec: fspec :=
    mk_simple (fun (n: nat) =>
                 ((fun varg o => (⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n /\ n < max⌝: iProp)%I),
                  (fun vret => (⌜vret = (Vint (Z.of_nat (5 * n)))↑⌝: iProp)%I))).
  Definition g_spec: fspec :=
    mk_simple (fun (n: nat) =>
                 ((fun varg o => (⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure n /\ n < max⌝: iProp)%I),
                  (fun vret => (⌜vret = (Vint (Z.of_nat (5 * n - 2)))↑⌝: iProp)%I))).
  Definition GlobalStb: gname -> option fspec := to_stb [("f", f_spec); ("g", g_spec)].

End PROOF.
