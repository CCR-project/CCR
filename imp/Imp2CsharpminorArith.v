From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
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

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Lemma map_val_vadd_comm
        src a b v
        (VADD: vadd a b = Some v)
        (WFOPS: checkOps a b)
    :
      Values.Val.addl (map_val src a) (map_val src b) = (map_val src v).
  Proof.
    destruct a; destruct b; ss; clarify.
    - ss. repeat f_equal.
      rewrite Int64.add_signed. f_equal. unfold_intrange_64.
      bsimpl. des.
      apply sumbool_to_bool_true in H.
      apply sumbool_to_bool_true in H0.
      apply sumbool_to_bool_true in WFOPS.
      apply sumbool_to_bool_true in WFOPS0.
      rewrite Int64.signed_repr; try (rewrite Int64.signed_repr); unfold_Int64_max_signed; unfold_Int64_min_signed; try nia.
    - uo; des_ifs. unfold scale_int in *. des_ifs. ss. unfold Ptrofs.of_int64 in *.
      f_equal. unfold map_ofs in *. unfold scale_ofs in *.
      unfold Z.divide in d. des. clarify. rewrite Z_div_mult in *; try nia.
      assert (COMM: (8 * z)%Z = (z * 8)%Z); try nia. rewrite <- COMM in *; clear COMM.
      rewrite Z.mul_add_distr_l in *. remember (8 * z)%Z as b. remember (8 * ofs)%Z as a.
      clear Heqb Heqa ofs z blk. move a before b.
      rename H into WFB, WFOPS into WFA.
      unfold_modrange_64. bsimpl; des.
      apply sumbool_to_bool_true in WFA.
      apply sumbool_to_bool_true in WFA0.
      apply sumbool_to_bool_true in WFB.
      apply sumbool_to_bool_true in WFB0.
      pose (Ptrofs.agree64_repr Heq (Int64.unsigned (Int64.repr a))) as aInt.
      pose (Ptrofs.agree64_repr Heq (Int64.unsigned (Int64.repr b))) as bInt.
      hexploit Ptrofs.agree64_add; auto.
      { eapply aInt. }
      { eapply bInt. }
      i. rename H into addInt.
      pose (Ptrofs.agree64_repr Heq (Int64.unsigned (Int64.repr (a + b)))) as abInt.
      rewrite <- Ptrofs.of_int64_to_int64 at 1; auto.
      rewrite <- Ptrofs.of_int64_to_int64; auto. f_equal.
      apply Ptrofs.agree64_to_int_eq in addInt. apply Ptrofs.agree64_to_int_eq in abInt.
      rewrite addInt; clear addInt. rewrite abInt; clear abInt. clear aInt bInt Heq.
      rewrite! Int64.repr_unsigned.
      rewrite Int64.add_unsigned. f_equal.
      rewrite Int64.unsigned_repr; try (rewrite Int64.unsigned_repr); unfold Int64.max_unsigned; unfold_Int64_modulus; try nia.
    - uo; des_ifs. unfold scale_int in *. des_ifs. ss. unfold Ptrofs.of_int64 in *.
      f_equal. unfold map_ofs in *. unfold scale_ofs in *.
      unfold Z.divide in d. des. clarify. rewrite Z_div_mult in *; try nia.
      assert (COMM: (8 * z)%Z = (z * 8)%Z); try nia. rewrite <- COMM in *; clear COMM.
      rewrite Z.mul_add_distr_l in *. remember (8 * z)%Z as b. remember (8 * ofs)%Z as a.
      clear Heqb Heqa ofs z blk. move a before b.
      rename H into WFB, WFOPS into WFA.
      unfold_modrange_64. bsimpl; des.
      apply sumbool_to_bool_true in WFA.
      apply sumbool_to_bool_true in WFA0.
      apply sumbool_to_bool_true in WFB.
      apply sumbool_to_bool_true in WFB0.
      pose (Ptrofs.agree64_repr Heq (Int64.unsigned (Int64.repr a))) as aInt.
      pose (Ptrofs.agree64_repr Heq (Int64.unsigned (Int64.repr b))) as bInt.
      hexploit Ptrofs.agree64_add; auto.
      { eapply aInt. }
      { eapply bInt. }
      i. rename H into addInt.
      pose (Ptrofs.agree64_repr Heq (Int64.unsigned (Int64.repr (a + b)))) as abInt.
      rewrite <- Ptrofs.of_int64_to_int64 at 1; auto.
      rewrite <- Ptrofs.of_int64_to_int64; auto. f_equal.
      apply Ptrofs.agree64_to_int_eq in addInt. apply Ptrofs.agree64_to_int_eq in abInt.
      rewrite addInt; clear addInt. rewrite abInt; clear abInt. clear aInt bInt Heq.
      rewrite! Int64.repr_unsigned.
      rewrite Int64.add_unsigned. f_equal.
      rewrite Int64.unsigned_repr; try (rewrite Int64.unsigned_repr); unfold Int64.max_unsigned; unfold_Int64_modulus; try nia.
  Qed.

  Lemma map_val_vsub_comm
        src a b v
        (VSUB: vsub a b = Some v)
        (WFOPS: checkOps a b)
    :
      Values.Val.subl (map_val src a) (map_val src b) = map_val src v.
  Proof.
    destruct a; destruct b; ss; clarify.
    - ss. repeat f_equal.
      rewrite Int64.sub_signed. f_equal. unfold_intrange_64.
      bsimpl. des.
      apply sumbool_to_bool_true in H.
      apply sumbool_to_bool_true in H0.
      apply sumbool_to_bool_true in WFOPS.
      apply sumbool_to_bool_true in WFOPS0.
      rewrite Int64.signed_repr; try (rewrite Int64.signed_repr); unfold_Int64_max_signed; unfold_Int64_min_signed; try nia.
    - uo; des_ifs. unfold scale_int in *. des_ifs. ss. unfold Ptrofs.of_int64 in *.
      f_equal. unfold map_ofs in *. unfold scale_ofs in *.
      unfold Z.divide in d. des. clarify. rewrite Z_div_mult in *; try nia.
      assert (COMM: (8 * z)%Z = (z * 8)%Z); try nia. rewrite <- COMM in *; clear COMM.
      rewrite Z.mul_sub_distr_l in *. remember (8 * z)%Z as b. remember (8 * ofs)%Z as a.
      clear Heqb Heqa ofs z blk. move a before b.
      rename H into WFB, WFOPS into WFA.
      unfold_modrange_64. bsimpl; des.
      apply sumbool_to_bool_true in WFA.
      apply sumbool_to_bool_true in WFA0.
      apply sumbool_to_bool_true in WFB.
      apply sumbool_to_bool_true in WFB0.
      pose (Ptrofs.agree64_repr Heq (Int64.unsigned (Int64.repr a))) as aInt.
      pose (Ptrofs.agree64_repr Heq (Int64.unsigned (Int64.repr b))) as bInt.
      hexploit Ptrofs.agree64_sub; auto.
      { eapply aInt. }
      { eapply bInt. }
      i. rename H into subInt.
      pose (Ptrofs.agree64_repr Heq (Int64.unsigned (Int64.repr (a - b)))) as abInt.
      rewrite <- Ptrofs.of_int64_to_int64 at 1; auto.
      rewrite <- Ptrofs.of_int64_to_int64; auto. f_equal.
      apply Ptrofs.agree64_to_int_eq in subInt. apply Ptrofs.agree64_to_int_eq in abInt.
      rewrite subInt; clear subInt. rewrite abInt; clear abInt. clear aInt bInt Heq.
      rewrite! Int64.repr_unsigned.
      unfold Int64.sub. f_equal.
      rewrite Int64.unsigned_repr; try (rewrite Int64.unsigned_repr); unfold Int64.max_unsigned; unfold_Int64_modulus; try nia.
    - uo; des_ifs.
      2:{ exfalso; apply n. f_equal. bsimpl. apply Nat.eqb_eq in Heq0. clarify. }
      apply Nat.eqb_eq in Heq0. clarify; ss. repeat f_equal.
      unfold Ptrofs.of_int64 in *. unfold map_ofs in *. unfold scale_ofs in *.
      rewrite Z.mul_sub_distr_l in *. remember (8 * ofs0)%Z as b. remember (8 * ofs)%Z as a.
      clear Heqb Heqa ofs ofs0 e blk0. move a before b.
      rename H into WFB, WFOPS into WFA.
      unfold_modrange_64. bsimpl; des.
      apply sumbool_to_bool_true in WFA.
      apply sumbool_to_bool_true in WFA0.
      apply sumbool_to_bool_true in WFB.
      apply sumbool_to_bool_true in WFB0.
      pose (Ptrofs.agree64_repr Heq (Int64.unsigned (Int64.repr a))) as aInt.
      pose (Ptrofs.agree64_repr Heq (Int64.unsigned (Int64.repr b))) as bInt.
      hexploit Ptrofs.agree64_sub; auto.
      { eapply aInt. }
      { eapply bInt. }
      i. rename H into subInt.
      apply Ptrofs.agree64_to_int_eq in subInt. rewrite subInt; clear subInt aInt bInt.
      unfold Int64.sub. f_equal. rewrite ! Int64.repr_unsigned.
      rewrite Int64.unsigned_repr; try (rewrite Int64.unsigned_repr); unfold Int64.max_unsigned; unfold_Int64_modulus; try nia.
  Qed.

  Lemma map_val_vmul_comm
        src a b v
        (VMUL: vmul a b = Some v)
        (WFOPS: checkOps a b)
    :
      Values.Val.mull (map_val src a) (map_val src b) = map_val src v.
  Proof.
    destruct a; destruct b; ss; clarify.
    ss. repeat f_equal.
    rename H into WFB, WFOPS into WFA.
    unfold_intrange_64. bsimpl; des.
    apply sumbool_to_bool_true in WFA.
    apply sumbool_to_bool_true in WFA0.
    apply sumbool_to_bool_true in WFB.
    apply sumbool_to_bool_true in WFB0.
    rewrite Int64.mul_signed. f_equal. unfold_intrange_64.
    rewrite Int64.signed_repr; try (rewrite Int64.signed_repr); unfold_Int64_max_signed; unfold_Int64_min_signed; try nia.
  Qed.

End ARITH.
