From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.

Require Import Imp2CsharpminorMatch.

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

  Definition modrange_63 (n: Z) := (- 1 < n < two_power_nat 63)%Z.

  Lemma int_to_mod_range
        (n : Z)
    :
      intrange_64 n -> modrange_64 (n mod modulus_64).
  Proof.
    i. unfold_intrange_64. unfold_modrange_64. set (two_power_nat 64) as P in *. des. split.
    - hexploit Z.mod_pos_bound.
      { instantiate (1:=P). subst P. pose (Coqlib.two_power_nat_pos 64). nia. }
      instantiate (1:=n). i. nia.
    - destruct (Z_lt_le_dec n 0).
      + clear H0. rewrite <- Z.opp_pos_neg in l. rewrite <- Z.opp_involutive in H. rewrite <- (Z.opp_involutive n).
        apply Zaux.Zopp_le_cancel in H. remember (- n)%Z as m. clear Heqm. clear n.
        assert (GTZERO: (m mod P > 0)%Z).
        { rewrite Z.mod_small; try nia. split; try nia.
          subst P. rewrite two_power_nat_S in *. remember (two_power_nat 63) as P. clear HeqP.
          assert (2 * P / 2 = P)%Z.
          { replace (2 * P)%Z with (P * 2)%Z by nia. eapply Z_div_mult. nia. }
          rewrite H0 in H. nia. }
        rewrite Z_mod_nz_opp_full.
        { rewrite <- Z.lt_sub_pos. nia. }
        nia.
      + clear H. apply Z.mod_pos_bound. pose (Coqlib.two_power_nat_pos 64). nia.
  Qed.

  Lemma unwrap_Ptrofs_Int64_z
        (z: Z)
        (LB: (0 <= z)%Z)
        (UB: intrange_64 z)
    :
      (Ptrofs.unsigned (Ptrofs.of_int64 (Int64.repr (z)))) = z.
  Proof.
    unfold_intrange_64. unfold Ptrofs.of_int64.
    hexploit (Int64.unsigned_repr z).
    { unfold Int64.max_unsigned. unfold_Int64_modulus. split; try nia. rewrite two_power_nat_equiv in *. ss. des.
      match goal with
      | [ UPB: (z <= ?_pow2 - 1)%Z |- _ ] => replace _pow2 with (2 ^ 63)%Z in *; ss; try nia
      end. }
    i. rewrite H. clear H.
    apply (Ptrofs.unsigned_repr z).
    unfold Ptrofs.max_unsigned. unfold_Ptrofs_modulus. des_ifs. split; try nia. rewrite two_power_nat_equiv in *. ss. des.
    match goal with
    | [ UPB: (z <= ?_pow2 - 1)%Z |- _ ] => replace _pow2 with (2 ^ 63)%Z in *; ss; try nia
    end.
  Qed.

  Lemma map_val_vadd_comm
        src a b v
        (VADD: vadd a b = Some v)
        (WFA: wf_val a)
        (WFB: wf_val b)
        (WFV: wf_val v)
    :
      Values.Val.addl (@map_val src a) (@map_val src b) = @map_val src v.
  Proof.
    destruct a; destruct b; ss; clarify.
    - ss. repeat f_equal.
      rewrite Int64.add_signed. f_equal. unfold_intrange_64.
      rewrite Int64.signed_repr; try (rewrite Int64.signed_repr); unfold_Int64_max_signed; unfold_Int64_min_signed; try nia.
    - uo; des_ifs. unfold scale_int in *. des_ifs. ss. unfold Ptrofs.of_int64 in *.
      f_equal. unfold map_ofs in *. unfold scale_ofs in *.
      unfold Z.divide in d. des. clarify. rewrite Z_div_mult in *; try nia.
      assert ((8 * z)%Z = (z * 8)%Z); try nia. rewrite <- H in *; clear H.
      rewrite Z.mul_add_distr_l in *. remember (8 * z)%Z as b. remember (8 * ofs)%Z as a.
      clear Heqb Heqa ofs z blk. move a before b.
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
      rewrite Int64.add_signed. f_equal. unfold_intrange_64.
      rewrite Int64.signed_repr; try (rewrite Int64.signed_repr); unfold_Int64_max_signed; unfold_Int64_min_signed; try nia.
    - uo; des_ifs. unfold scale_int in *. des_ifs. ss. unfold Ptrofs.of_int64 in *.
      f_equal. unfold map_ofs in *. unfold scale_ofs in *.
      unfold Z.divide in d. des. clarify. rewrite Z_div_mult in *; try nia.
      assert ((8 * z)%Z = (z * 8)%Z); try nia. rewrite <- H in *; clear H.
      rewrite Z.mul_add_distr_l in *. remember (8 * z)%Z as b. remember (8 * ofs)%Z as a.
      clear Heqb Heqa ofs z blk. move a before b.
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
      rewrite Int64.add_signed. f_equal. unfold_intrange_64.
      rewrite Int64.signed_repr; try (rewrite Int64.signed_repr); unfold_Int64_max_signed; unfold_Int64_min_signed; try nia.
  Qed.

End ARITH.


