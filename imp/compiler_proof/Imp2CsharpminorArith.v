From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.

Require Import Imp2Csharpminor.
Require Import Imp2CsharpminorMatch.
Require Import Imp2CsharpminorGenv.

From compcert Require Import Csharpminor.

Set Implicit Arguments.

Ltac unfold_Int64_modulus := unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize in *.
Ltac unfold_Int64_max_signed := unfold Int64.max_signed, Int64.half_modulus in *; unfold_Int64_modulus.
Ltac unfold_Int64_min_signed := unfold Int64.min_signed, Int64.half_modulus in *; unfold_Int64_modulus.
Ltac unfold_Ptrofs_modulus := unfold Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize in *.
Ltac unfold_Ptrofs_half_modulus := unfold Ptrofs.half_modulus in *; unfold_Ptrofs_modulus.
Ltac unfold_Int_modulus := unfold Int.modulus, Int.wordsize, Wordsize_32.wordsize in *.
Ltac unfold_Int_max_signed := unfold Int.max_signed, Int.half_modulus in *; unfold_Int_modulus.
Ltac unfold_Int_min_signed := unfold Int.min_signed, Int.half_modulus in *; unfold_Int_modulus.

Section ARITH.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Lemma int64_ptrofs :
    Ptrofs.modulus = Int64.modulus.
  Proof. unfold_Int64_modulus. unfold_Ptrofs_modulus. des_ifs. Qed.

  Lemma int64_ext
        i0 i1
        (INTVAL: (Int64.intval i0) = (Int64.intval i1))
    :
      i0 = i1.
  Proof.
    destruct i0, i1. ss. clarify. f_equal. apply proof_irrelevance.
  Qed.

  Lemma int64_mod_ext
        i0 i1
        (INTVAL: ((Int64.intval i0) mod Int64.modulus)%Z = ((Int64.intval i1) mod Int64.modulus)%Z)
    :
      i0 = i1.
  Proof.
    destruct i0, i1. ss. rewrite Z.mod_small in INTVAL; try lia. rewrite Z.mod_small in INTVAL; try lia.
    eapply int64_ext; eauto.
  Qed.

  Lemma ptrofs_ext
        i0 i1
        (INTVAL: (Ptrofs.intval i0) = (Ptrofs.intval i1))
    :
      i0 = i1.
  Proof.
    destruct i0, i1. ss. clarify. f_equal. apply proof_irrelevance.
  Qed.

  Lemma ptrofs_mod_ext
        i0 i1
        (INTVAL: ((Ptrofs.intval i0) mod Ptrofs.modulus)%Z = ((Ptrofs.intval i1) mod Ptrofs.modulus)%Z)
    :
      i0 = i1.
  Proof.
    destruct i0, i1. ss. rewrite Z.mod_small in INTVAL; try lia. rewrite Z.mod_small in INTVAL; try lia.
    eapply ptrofs_ext; eauto.
  Qed.

  Lemma unwrap_Ptrofs_Int64_z
        (z: Z)
        (UB: modrange_64 z = true)
    :
      (Ptrofs.unsigned (Ptrofs.of_int64 (Int64.repr (z)))) = z.
  Proof.
    unfold_modrange_64. bsimpl. des.
    apply sumbool_to_bool_true in UB.
    apply sumbool_to_bool_true in UB0.
    unfold Ptrofs.of_int64.
    hexploit (Int64.unsigned_repr z).
    { unfold Int64.max_unsigned. unfold_Int64_modulus. split; try nia. }
    i. rewrite H. clear H.
    apply (Ptrofs.unsigned_repr z).
    unfold Ptrofs.max_unsigned. unfold_Ptrofs_modulus. des_ifs. split; try nia.
  Qed.

  Lemma unwrap_Ptrofs_repr_z
        z
        (UB: modrange_64 z = true)
    :
      (Ptrofs.unsigned (Ptrofs.repr z)) = z.
  Proof.
    unfold_modrange_64. bsimpl. des.
    apply sumbool_to_bool_true in UB.
    apply sumbool_to_bool_true in UB0.
    apply Ptrofs.unsigned_repr.
    unfold Ptrofs.max_unsigned. unfold_Ptrofs_modulus. des_ifs. lia.
  Qed.

  Lemma map_val_vadd_comm
        src a b v
        (VADD: vadd a b = Some v)
    :
      Values.Val.addl (map_val src a) (map_val src b) = (map_val src v).
  Proof.
    destruct a; destruct b; ss; clarify.
    - ss. repeat f_equal.
      unfold Int64.add.
      rewrite ! Int64.unsigned_repr_eq.
      apply int64_mod_ext.
      f_equal.
      Local Transparent Int64.repr.
      ss. rewrite ! Int64.Z_mod_modulus_eq.
      rewrite <- Z.add_mod; try lia.
      unfold_Int64_modulus. ss.
      Local Opaque Int64.repr.
    - uo; des_ifs. unfold scale_int in *. des_ifs. ss.
      unfold Ptrofs.of_int64 in *.
      f_equal. unfold map_ofs in *.
      unfold scale_ofs in *.
      unfold Z.divide in d. des. clarify. rewrite Z_div_mult in *; try nia.
      assert (COMM: (8 * z)%Z = (z * 8)%Z); try nia. rewrite <- COMM in *; clear COMM.
      rewrite Z.mul_add_distr_l in *. remember (8 * z)%Z as b. remember (8 * ofs)%Z as a.
      clear Heqb Heqa ofs z blk. move a before b.
      rewrite Int64.unsigned_repr_eq.
      rewrite <- int64_ptrofs.
      unfold Ptrofs.add. rewrite <- Ptrofs.unsigned_repr_eq.
      rewrite Ptrofs.repr_unsigned. rewrite ! Ptrofs.unsigned_repr_eq.
      apply ptrofs_ext.
      Local Transparent Ptrofs.repr.
      ss. rewrite ! Ptrofs.Z_mod_modulus_eq.
      rewrite <- Z.add_mod; try lia.
      unfold_Ptrofs_modulus. ss.
      Local Opaque Ptrofs.repr.
    - uo; des_ifs. unfold scale_int in *. des_ifs. ss.
      unfold Ptrofs.of_int64 in *.
      f_equal. unfold map_ofs in *.
      unfold scale_ofs in *.
      unfold Z.divide in d. des. clarify. rewrite Z_div_mult in *; try nia.
      assert (COMM: (8 * z)%Z = (z * 8)%Z); try nia. rewrite <- COMM in *; clear COMM.
      rewrite Z.mul_add_distr_l in *. remember (8 * z)%Z as b. remember (8 * ofs)%Z as a.
      clear Heqb Heqa ofs z blk. move a before b.
      rewrite Int64.unsigned_repr_eq.
      rewrite <- int64_ptrofs.
      unfold Ptrofs.add. rewrite <- Ptrofs.unsigned_repr_eq.
      rewrite Ptrofs.repr_unsigned. rewrite ! Ptrofs.unsigned_repr_eq.
      apply ptrofs_ext.
      Local Transparent Ptrofs.repr.
      ss. rewrite ! Ptrofs.Z_mod_modulus_eq.
      rewrite <- Z.add_mod; try lia.
      unfold_Ptrofs_modulus. ss.
      Local Opaque Ptrofs.repr.
  Qed.

  Lemma map_val_vsub_comm
        src a b v
        (VSUB: vsub a b = Some v)
    :
      Values.Val.subl (map_val src a) (map_val src b) = map_val src v.
  Proof.
    Local Transparent Int64.repr. Local Transparent Ptrofs.repr.
    destruct a; destruct b; ss; clarify.
    - ss. repeat f_equal.
      unfold Int64.sub. rewrite ! Int64.unsigned_repr_eq.
      apply int64_mod_ext. f_equal.
      ss. rewrite ! Int64.Z_mod_modulus_eq.
      rewrite <- Zminus_mod; try lia.
    - uo; des_ifs. unfold scale_int in *. des_ifs. ss. unfold Ptrofs.of_int64 in *.
      f_equal. unfold map_ofs in *. unfold scale_ofs in *.
      unfold Z.divide in d. des. clarify. rewrite Z_div_mult in *; try nia.
      assert (COMM: (8 * z)%Z = (z * 8)%Z); try nia. rewrite <- COMM in *; clear COMM.
      rewrite Z.mul_sub_distr_l in *. remember (8 * z)%Z as b. remember (8 * ofs)%Z as a.
      clear Heqb Heqa ofs z blk. move a before b.
      rewrite Int64.unsigned_repr_eq.
      rewrite <- int64_ptrofs.
      unfold Ptrofs.sub. rewrite <- Ptrofs.unsigned_repr_eq.
      rewrite Ptrofs.repr_unsigned. rewrite ! Ptrofs.unsigned_repr_eq.
      apply ptrofs_ext.
      ss. rewrite ! Ptrofs.Z_mod_modulus_eq.
      rewrite <- Zminus_mod; try lia.
    - uo; des_ifs.
      2:{ exfalso; apply n. f_equal. bsimpl. apply Nat.eqb_eq in Heq0. clarify. }
      apply Nat.eqb_eq in Heq0. clarify; ss. repeat f_equal.
      unfold Ptrofs.of_int64 in *. unfold map_ofs in *. unfold scale_ofs in *.
      rewrite Z.mul_sub_distr_l in *. remember (8 * ofs0)%Z as b. remember (8 * ofs)%Z as a.
      clear Heqb Heqa ofs ofs0 e blk0. move a before b.
      unfold Ptrofs.to_int64.
      unfold Ptrofs.sub. ss.
      rewrite ! Ptrofs.Z_mod_modulus_eq.
      rewrite ! int64_ptrofs. rewrite <- Zminus_mod.
      apply int64_mod_ext.
      ss. rewrite ! Int64.Z_mod_modulus_eq.
      rewrite ! Zmod_mod. ss.
      Local Opaque Int64.repr. Local Opaque Ptrofs.repr.
  Qed.

  Lemma map_val_vmul_comm
        src a b v
        (VMUL: vmul a b = Some v)
    :
      Values.Val.mull (map_val src a) (map_val src b) = map_val src v.
  Proof.
    Local Transparent Int64.repr.
    destruct a; destruct b; ss; clarify.
    ss. repeat f_equal.
    unfold Int64.mul. rewrite ! Int64.unsigned_repr_eq.
    apply int64_mod_ext. f_equal.
    ss. rewrite ! Int64.Z_mod_modulus_eq.
    rewrite <- Zmult_mod; try lia.
    Local Opaque Int64.repr.
  Qed.

End ARITH.
