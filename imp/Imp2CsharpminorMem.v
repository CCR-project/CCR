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
Require Import Mem0.

Require Import Imp2Csharpminor.
Require Import Imp2CsharpminorMatch.
Require Import Imp2CsharpminorArith.

From compcert Require Import Csharpminor.

Set Implicit Arguments.


Section MEM.

  Context `{Σ: GRA.t}.
  Context `{builtins: builtinsTy}.

  Hypothesis map_blk_after_init :
    forall src blk
      (COMP : exists tgt, compile src = OK tgt)
      (ALLOCED : blk >= (src_init_nb src)),
      (<<ALLOCMAP: (map_blk src blk) = Pos.of_succ_nat (tgt_init_len + (ext_len src) + (int_len src - sk_len src) + blk)>>).

  Hypothesis map_blk_inj :
    forall src b1 b2
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (WFPROG: (incl (name1 src.(defsL)) ((name1 src.(prog_varsL)) ++ (name2 src.(prog_funsL)))))
      (WFSK: Sk.wf src.(defsL)),
      <<INJ: map_blk src b1 = map_blk src b2 -> b1 = b2>>.

  Variable src : Imp.programL.
  Variable m : Mem.t.
  Variable tm : Mem.mem.
  Context {MM: match_mem src m tm}.
  Context {WFPROG: (incl (name1 src.(defsL)) ((name1 src.(prog_varsL)) ++ (name2 src.(prog_funsL))))}.
  Context {WFSK: Sk.wf src.(defsL)}.
  Context {COMP : exists tgt, compile src = OK tgt}.

  Lemma match_mem_alloc
        n m2 blk tm2 tblk
        (SMEM: (blk, m2) = Mem.alloc m n)
        (TMEM: (tm2, tblk) = Memory.Mem.alloc tm (- size_chunk Mptr) (map_ofs n))
    :
      (<<MM2: match_mem src m2 tm2>>).
  Proof.
    inv MM. inv SMEM. split; i; ss; try split.
    - lia.
    - hexploit Mem.nextblock_alloc; eauto. i. rewrite H. rewrite NBLK.
      hexploit map_blk_after_init.
      { eauto. }
      { instantiate (1:= Mem.nb m). lia. }
      hexploit map_blk_after_init.
      { eauto. }
      { instantiate (1:= S (Mem.nb m)). lia. }
      i. rewrite H1. rewrite H0. lia.
    - rename H into SMEM. pose (NPeano.Nat.eq_dec (Mem.nb m) blk) as BLK. destruct BLK.
      + clarify; ss. unfold update in SMEM. des_ifs. clear e. des. clarify. ss. rewrite <- NBLK.
        rewrite andb_true_iff in Heq. des. rewrite Z.leb_le in Heq. rewrite Z.ltb_lt in Heq0.
        rename Heq into LB. rename Heq0 into UB.
        hexploit Mem.load_alloc_same'; ss; eauto.
        { unfold size_chunk. des_ifs. instantiate (1:=map_ofs ofs). unfold map_ofs. nia. }
        { instantiate (1:=Mint64). unfold size_chunk. des_ifs. unfold map_ofs in *. nia. }
        { unfold align_chunk. des_ifs. unfold map_ofs. unfold Z.divide. exists ofs. nia. }
        i. hexploit Mem.alloc_result; eauto. i. clarify.
      + unfold update in SMEM. des_ifs. clear n0. rename n1 into BLK. apply MMEM in SMEM. des.
        hexploit Mem.load_alloc_other; eauto.
    - rename H into SMEM. pose (NPeano.Nat.eq_dec (Mem.nb m) blk) as BLK. destruct BLK.
      + clarify; ss. unfold update in SMEM. des_ifs. clear e. des. clarify. rewrite <- NBLK.
        rewrite andb_true_iff in Heq. des. rewrite Z.leb_le in Heq. rewrite Z.ltb_lt in Heq0.
        rename Heq into LB. rename Heq0 into UB.
        hexploit Mem.valid_access_alloc_same; eauto.
        { unfold size_chunk. des_ifs. instantiate (1:=map_ofs ofs). unfold map_ofs. nia. }
        { instantiate (1:=Mint64). unfold size_chunk. des_ifs. unfold map_ofs in *. nia. }
        { unfold align_chunk. des_ifs. unfold map_ofs. unfold Z.divide. exists ofs. nia. }
        i. hexploit Mem.alloc_result; eauto. i. clarify. hexploit Mem.valid_access_freeable_any; eauto.
      + unfold update in SMEM. des_ifs. clear n0. rename n1 into BLK. apply MMEM in SMEM. des.
        hexploit Mem.valid_access_alloc_other; eauto.
  Qed.

  Lemma match_mem_malloc
        n m2 blk tm2
        (SMEM: (blk, m2) = Mem.alloc m n)
        (TMEM : Memory.Mem.store Mptr (fst (Memory.Mem.alloc tm (- size_chunk Mptr) (map_ofs n)))
                                 (snd (Memory.Mem.alloc tm (- size_chunk Mptr) (map_ofs n))) (- size_chunk Mptr)
                                 (Values.Vlong (Int64.repr (map_ofs n))) = Some tm2)
    :
      <<MM2: match_mem src m2 tm2>>.
  Proof.
    unfold map_ofs in *. remember (Memory.Mem.alloc tm (- size_chunk Mptr) (8 * n)) as tm1. destruct tm1 as [tm1 tblk].
    hexploit match_mem_alloc; eauto. i. inv H. split; i; try split.
    - lia.
    - rewrite <- NBLK. eapply Mem.nextblock_store; eauto.
    - rename H into SRCM. pose (NPeano.Nat.eq_dec blk blk0) as BLK. destruct BLK.
      + clarify; ss. unfold map_ofs in *. unfold size_chunk in *. des_ifs; ss.
        pose (Z_le_gt_dec 0 (8 * ofs)) as OFS. destruct OFS.
        * erewrite Mem.load_store_other; eauto. apply MMEM in SRCM. des. eauto.
        * depgen SMEM. depgen g. depgen SRCM. clear. i. unfold Mem.alloc in SMEM. inv SMEM. ss.
          unfold update in SRCM. des_ifs. nia.
      + erewrite Mem.load_store_other; eauto.
        * apply MMEM in SRCM. des; eauto.
        * left. sym in Heqtm1. apply Mem.alloc_result in Heqtm1. clarify. ss.
          unfold Mem.alloc in SMEM. inv SMEM. ss. inv MM. rewrite NBLK0. depgen n0. depgen map_blk_inj.
          ii. apply map_blk_inj in H; eauto. 
    - apply MMEM in H; des. hexploit Mem.store_valid_access_1; eauto. 
  Qed.

  Lemma match_mem_free
        blk ofs m2
        (SMEM: Mem.free m blk ofs = Some m2)
    :
      (<<MM2: match_mem src m2 tm>>).
  Proof.
    inv MM. unfold Mem.free in SMEM. des_ifs. apply MMEM in Heq. des.
    split; i; eauto. ss. unfold update in H. des_ifs; eauto.
  Qed.

  Lemma match_mem_store
        blk ofs v m2
        (SMEM: Mem.store m blk ofs v = Some m2)
    :
      exists tm2,
        ((<<TMEM: Memory.Mem.store Mint64 tm (map_blk src blk) (map_ofs ofs) (map_val src v) = Some tm2>>) /\
        (<<MM2: match_mem src m2 tm2>>)).
  Proof.
    inv MM. unfold Mem.store in SMEM. des_ifs. hexploit MMEM; eauto. i; des.
    hexploit (Mem.valid_access_store tm Mint64 (map_blk src blk) (map_ofs ofs) (map_val src v)); eauto.
    i. dependent destruction X. rename x into tm2. rename e into TGTM2. exists tm2. split; auto. try split; i; try split; ss; eauto.
    - erewrite Mem.nextblock_store; eauto.
    - des_ifs.
      + des; clarify; ss. bsimpl. des. apply sumbool_to_bool_true in Heq0. apply sumbool_to_bool_true in Heq1. clarify.
        erewrite Mem.load_store_same; eauto. unfold map_val. ss. des_ifs.
      + bsimpl. des.
        * apply sumbool_to_bool_false in Heq0. hexploit Mem.load_store_other; eauto.
          { left. instantiate (1:= map_blk src blk0). ii. apply map_blk_inj in H0; eauto. }
          i. erewrite H0. apply MMEM in H. des. eauto.
        * apply sumbool_to_bool_false in Heq0. hexploit Mem.load_store_other; eauto.
          2:{ i. erewrite H0. apply MMEM in H. des. eauto. }
          right. ss. unfold map_ofs in *. lia.
    - des_ifs.
      + des; clarify; ss. bsimpl. des. apply sumbool_to_bool_true in Heq0. apply sumbool_to_bool_true in Heq1. clarify.
        split; auto. eapply Mem.store_valid_access_1; eauto.
      + bsimpl. des.
        * apply sumbool_to_bool_false in Heq0. apply MMEM in H; des. split; auto. eapply Mem.store_valid_access_1; eauto.
        * apply sumbool_to_bool_false in Heq0. apply MMEM in H; des. split; auto. eapply Mem.store_valid_access_1; eauto.
  Qed.

  Lemma valid_ptr_contra
        blk ofs
        (WFOFS: modrange_64 (scale_ofs ofs))
        (SRC: Mem.valid_ptr m blk ofs = true)
        (TGT: Mem.valid_pointer tm (map_blk src blk) (Ptrofs.unsigned (Ptrofs.repr (map_ofs ofs))) = false)
    :
      False.
  Proof.
    unfold Mem.valid_ptr in SRC. unfold is_some in SRC. des_ifs.
    inv MM. apply MMEM in Heq. des. clear MMEM. unfold map_ofs in *.
    unfold scale_ofs in WFOFS.
    rewrite unwrap_Ptrofs_repr_z in TGT; try nia; auto.
    rename TGT into CONTRA.
    match goal with [ CONTRA: ?vp = false |- _ ] => assert (CONTRA2: vp = true) end.
    { rewrite Mem.valid_pointer_nonempty_perm. eapply Mem.valid_access_perm in TVALID.
      hexploit Mem.perm_implies; eauto. econs. }
    clarify.
  Qed.

  Lemma valid_ptr_wf_ofs
        blk ofs
        (VACC : Mem.valid_ptr m blk ofs = true)
    :
      (0 <= ofs)%Z.
  Proof.
    unfold Mem.valid_ptr in VACC. unfold is_some in VACC. des_ifs. inv MM. eapply MMEM in Heq; des; eauto.
  Qed.

  Lemma match_mem_cmp
        a b tf
        (WFA: wf_val a)
        (WFB: wf_val b)
        (SRCCMP: vcmp m a b = Some tf)
    :
      Values.Val.cmplu (Mem.valid_pointer tm) Ceq (map_val src a) (map_val src b) =
      if (tf) then Some (Values.Vtrue) else Some (Values.Vfalse).
  Proof.
    destruct a eqn:DESA; destruct b eqn:DESB; destruct tf; clarify; unfold vcmp in SRCCMP; des_ifs.
    - apply sumbool_to_bool_true in H0. clarify; ss.
      unfold Values.Val.cmplu. ss. unfold Values.Val.of_bool. rewrite Int64.eq_true. ss.
    - apply sumbool_to_bool_false in H0. clarify; ss.
      unfold Values.Val.cmplu. ss. unfold Values.Val.of_bool. rewrite Int64.signed_eq.
      unfold_intrange_64. bsimpl. des.
      apply sumbool_to_bool_true in WFA.
      apply sumbool_to_bool_true in WFA0.
      apply sumbool_to_bool_true in WFB.
      apply sumbool_to_bool_true in WFB0.
      rewrite! Int64.signed_repr.
      2,3: unfold_Int64_min_signed; unfold_Int64_max_signed; try nia.
      des_ifs. apply Coqlib.proj_sumbool_true in Heq; clarify.
    - clear SRCCMP. bsimpl. des. apply sumbool_to_bool_true in Heq0. clarify.
      unfold Values.Val.cmplu. ss. des_ifs. bsimpl. des. exfalso. eapply valid_ptr_contra; eauto.
    - clear SRCCMP. bsimpl. des. apply sumbool_to_bool_true in Heq0. clarify.
      unfold Values.Val.cmplu. ss. des_ifs. bsimpl. des. exfalso. eapply valid_ptr_contra; eauto.
    - bsimpl. des. apply sumbool_to_bool_true in H0; clarify. apply sumbool_to_bool_true in H1; clarify; clarify.
      clear Heq. unfold Values.Val.cmplu. ss. des_ifs; bsimpl; des.
      all: try (rewrite Ptrofs.eq_true; ss).
      all: exfalso; eapply valid_ptr_contra; eauto.
    - bsimpl; des.
      + apply sumbool_to_bool_false in H0. rename H0 into BLK. unfold Values.Val.cmplu. ss. des_ifs.
        1,2: apply map_blk_inj in e; clarify.
        bsimpl. des.
        { pose (valid_ptr_contra _ _ WFA Heq Heq2). clarify. }
        { pose (valid_ptr_contra _ _ WFB Heq0 Heq2). clarify. }
      + apply sumbool_to_bool_false in H0. rename H0 into OFS. unfold Values.Val.cmplu. ss. des_ifs.
        { apply map_blk_inj in e; clarify. ss.
          unfold Ptrofs.eq. hexploit (valid_ptr_wf_ofs _ _ Heq); i. hexploit (valid_ptr_wf_ofs _ _ Heq0); i.
          unfold map_ofs in *. rewrite! unwrap_Ptrofs_repr_z; try nia; eauto. erewrite Coqlib.zeq_false; try lia. ss. }
        { bsimpl; des.
          - pose (valid_ptr_contra _ _ WFA Heq Heq2). clarify.
          - pose (valid_ptr_contra _ _ WFB Heq0 Heq2). clarify. }
        { bsimpl; des.
          - pose (valid_ptr_contra _ _ WFA Heq Heq2). clarify.
          - pose (valid_ptr_contra _ _ WFB Heq0 Heq2). clarify. }
  Qed.

End MEM.
