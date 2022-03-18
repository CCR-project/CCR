Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import Imp2Csharpminor.
Require Import Imp2CsharpminorGenv.

Import Permutation.

From compcert Require Import AST Csharpminor Globalenvs Linking.

Set Implicit Arguments.



Section DECOMP.

  Context `{builtins: builtinsTy}.

  Lemma ext_vars_names :
    forall src, <<EVN: List.map fst (compile_eVars (ext_varsL src)) = List.map s2p (ext_varsL src)>>.
  Proof.
    i. unfold compile_eVars. rewrite List.map_map. apply List.map_ext. i. ss.
  Qed.

  Lemma ext_funs_names :
    forall src, <<EFN: List.map fst (compile_eFuns (ext_funsL src)) = List.map (s2p ∘ fst) (ext_funsL src)>>.
  Proof.
    i. unfold compile_eFuns. rewrite List.map_map. apply List.map_ext. i. destruct a. ss.
  Qed.

  Lemma int_vars_names :
    forall src, <<IVN: List.map fst (compile_iVars (prog_varsL src)) = List.map (s2p ∘ fst) (prog_varsL src)>>.
  Proof.
    i. unfold compile_iVars. rewrite List.map_map. apply List.map_ext. i. destruct a; ss.
  Qed.

  Lemma int_funs_names :
    forall src, <<IFN: List.map fst (compile_iFuns (prog_funsL src)) = List.map (s2p ∘ (fst ∘ snd)) (prog_funsL src)>>.
  Proof.
    i. unfold compile_iFuns. rewrite List.map_map. apply List.map_ext. i. destruct a. destruct p. ss.
  Qed.

  Lemma decomp_init_g :
    forall id gd (INTGT: In (id, gd) init_g),
      (<<BTS: exists fd, (id = s2p (fst fd)) /\ (gd = snd fd) /\ (In fd bts)>>) \/
      (<<MALLOC: (id = s2p "malloc") /\ (gd = Gfun (External EF_malloc))>>) \/
      (<<FREE: (id = s2p "free") /\ (gd = Gfun (External EF_free))>>).
  Proof.
    Local Transparent init_g. Local Transparent init_g0.
    i. unfold init_g in INTGT. unfold init_g0 in INTGT. rewrite map_app in INTGT.
    rewrite in_app_iff in INTGT. des.
    { left. apply Coqlib.list_in_map_inv in INTGT. des. exists x; auto. destruct x; ss; clarify; eauto. }
    ss. des; clarify; eauto.
    Local Opaque init_g0. Local Opaque init_g.
  Qed.

  Lemma decomp_c_sys :
    forall id gd (INTGT: In (id, gd) c_sys),
      (<<SYS: exists fd, (compile_eFun fd = (id, gd)) /\ (In fd syscalls)>>).
  Proof.
    i. unfold c_sys in INTGT. eapply Coqlib.list_in_map_inv in INTGT. des. exists x; eauto.
  Qed.

  Lemma decomp_efs :
    forall src id gd (INTGT: In (id, gd) (compile_eFuns (ext_funsL src))),
      (<<EFS: exists fd, (compile_eFun fd = (id, gd)) /\ (In fd (ext_funsL src))>>).
  Proof.
    i. unfold compile_eFuns in INTGT. eapply Coqlib.list_in_map_inv in INTGT. des. exists x; eauto.
  Qed.

  Lemma decomp_evs :
    forall src id gd (INTGT: In (id, gd) (compile_eVars (ext_varsL src))),
      (<<EVS: exists vd, (compile_eVar vd = (id, gd)) /\ (In vd (ext_varsL src))>>).
  Proof.
    i. unfold compile_eVars in INTGT. eapply Coqlib.list_in_map_inv in INTGT. des. exists x; eauto.
  Qed.

  Lemma decomp_ifs :
    forall src id gd (INTGT: In (id, gd) (compile_iFuns (prog_funsL src))),
      (<<IFS: exists fd, (compile_iFun fd = (id, gd)) /\ (In fd (prog_funsL src))>>).
  Proof.
    i. unfold compile_iFuns in INTGT. eapply Coqlib.list_in_map_inv in INTGT. des. exists x; eauto.
  Qed.

  Lemma decomp_ivs :
    forall src id gd (INTGT: In (id, gd) (compile_iVars (prog_varsL src))),
      (<<IVS: exists vd, (compile_iVar vd = (id, gd)) /\ (In vd (prog_varsL src))>>).
  Proof.
    i. unfold compile_iVars in INTGT. eapply Coqlib.list_in_map_inv in INTGT. des. exists x; eauto.
  Qed.

  Lemma decomp_gdefs :
    forall src id gd (INTGT : In (id, gd) (compile_gdefs src)),
      (<<BTS: exists fd, (id = s2p (fst fd)) /\ (gd = snd fd) /\ (In fd bts)>>) \/
      (<<MALLOC: (id = s2p "malloc") /\ (gd = Gfun (External EF_malloc))>>) \/
      (<<FREE: (id = s2p "free") /\ (gd = Gfun (External EF_free))>>) \/
      (<<SYS: exists fd, (compile_eFun fd = (id, gd)) /\ (In fd syscalls)>>) \/
      (<<EFS: exists fd, (compile_eFun fd = (id, gd)) /\ (In fd (ext_funsL src))>>) \/
      (<<EVS: exists vd, (compile_eVar vd = (id, gd)) /\ (In vd (ext_varsL src))>>) \/
      (<<IFS: exists fd, (compile_iFun fd = (id, gd)) /\ (In fd (prog_funsL src))>>) \/
      (<<IVS: exists vd, (compile_iVar vd = (id, gd)) /\ (In vd (prog_varsL src))>>).
  Proof.
    i. unfold compile_gdefs in INTGT.
    apply in_app_or in INTGT. des.
    { apply decomp_init_g in INTGT. des; auto.
      - left; eauto.
      - do 2 right; left; eauto. }
    apply in_app_or in INTGT. des.
    { apply decomp_c_sys in INTGT. auto. }
    apply in_app_or in INTGT. des.
    { apply decomp_efs in INTGT. do 3 right. auto. }
    apply in_app_or in INTGT. des.
    { apply decomp_evs in INTGT. do 4 right. auto. }
    apply in_app_or in INTGT. des.
    { apply decomp_ifs in INTGT. do 5 right. auto. }
    apply decomp_ivs in INTGT. do 6 right. auto.
  Qed.

  Lemma decomp_gdefs_split :
    forall src id gd (INTGT : In (id, gd) (compile_gdefs src)),
      ((<<INITG: In id (name1 init_g)>>) /\
       ((<<BTS: exists fd, (id = s2p (fst fd)) /\ (gd = snd fd) /\ (In fd bts)>>) \/
        (<<MALLOC: (id = s2p "malloc") /\ (gd = Gfun (External EF_malloc))>>) \/
        (<<FREE: (id = s2p "free") /\ (gd = Gfun (External EF_free))>>)))
      \/
      (<<SYS: exists fd, (compile_eFun fd = (id, gd)) /\ (In fd syscalls)>>)
      \/
      (<<EFS: exists fd, (compile_eFun fd = (id, gd)) /\ (In fd (ext_funsL src))>>) \/
      (<<EVS: exists vd, (compile_eVar vd = (id, gd)) /\ (In vd (ext_varsL src))>>) \/
      (<<IFS: exists fd, (compile_iFun fd = (id, gd)) /\ (In fd (prog_funsL src))>>) \/
      (<<IVS: exists vd, (compile_iVar vd = (id, gd)) /\ (In vd (prog_varsL src))>>).
  Proof.
    Local Transparent init_g. Local Transparent init_g0.
    i. hexploit decomp_gdefs; eauto. i. des; eauto.
    - left. split; eauto.
      2:{ left. eauto. }
      red. unfold init_g, init_g0. unfold name1; rewrite List.map_map.
      repeat rewrite map_app. rewrite in_app_iff. left. destruct fd; clarify; ss.
      match goal with
      | [ BTS0: In _ bts |- In _ (List.map ?mapf _) ] => apply (in_map mapf) in BTS0; ss end.
    - left. split; eauto. red. unfold init_g, init_g0. unfold name1; rewrite List.map_map.
      repeat rewrite map_app. rewrite in_app_iff. right. ss. eauto.
    - left. split; eauto. red. unfold init_g, init_g0. unfold name1; rewrite List.map_map.
      repeat rewrite map_app. rewrite in_app_iff. right. ss. eauto.
    - right. eauto.
    - do 2 right. eauto.
    - do 3 right. eauto.
    - do 4 right. eauto.
    - do 5 right. eauto.
      Local Opaque init_g0. Local Opaque init_g.
  Qed.

  Lemma has_malloc :
    forall src, (<<MALLOC: In (s2p "malloc", Gfun (External EF_malloc)) (compile_gdefs src)>>).
  Proof.
    i. unfold compile_gdefs. apply in_or_app. left.
    Local Transparent init_g. Local Transparent init_g0.
    unfold init_g. unfold init_g0. rewrite map_app. rewrite in_app_iff. right. ss. left; ss.
    Local Opaque init_g0. Local Opaque init_g.
  Qed.

  Lemma has_free :
    forall src, (<<FREE: In (s2p "free", Gfun (External EF_free)) (compile_gdefs src)>>).
  Proof.
    i. unfold compile_gdefs. apply in_or_app. left.
    Local Transparent init_g. Local Transparent init_g0.
    unfold init_g. unfold init_g0. rewrite map_app. rewrite in_app_iff. right. ss. right; eauto.
    Local Opaque init_g0. Local Opaque init_g.
  Qed.

  Lemma has_bts :
    forall src id bt, In (id, bt) bts -> In (s2p id, bt) (compile_gdefs src).
  Proof.
    i. unfold compile_gdefs. apply in_or_app. left.
    Local Transparent init_g. Local Transparent init_g0.
    unfold init_g. unfold init_g0. rewrite map_app. rewrite in_app_iff. left.
    Local Opaque init_g0. Local Opaque init_g.
    apply (in_map (fun '(name, fd) => (s2p name, fd))) in H; auto.
  Qed.

  Lemma in_bts_in_init_g
        fd
        (IN: In fd bts)
    :
      <<INITG: In (s2p (fst fd), snd fd) init_g>>.
  Proof.
    red. destruct fd; ss; clarify.
    Local Transparent init_g. Local Transparent init_g0.
    unfold init_g. unfold init_g0. rewrite map_app. rewrite in_app_iff. left.
    Local Opaque init_g0. Local Opaque init_g.
    apply (in_map (fun '(name, fd) => (s2p name, fd))) in IN; auto.
  Qed.

  Lemma norepet_unique {A} {B} :
    forall (l : list (A * B)) id gd1 gd2
      (NOREPET : Coqlib.list_norepet (List.map fst l))
      (IN1: In (id, gd1) l)
      (IN2: In (id, gd2) l),
      gd1 = gd2.
  Proof.
    induction l; i; ss; clarify.
    des; ss; clarify.
    - inv NOREPET. apply (in_map fst) in IN1. ss.
    - inv NOREPET. apply (in_map fst) in IN2. ss.
    - inv NOREPET. destruct a; ss. eapply IHl; eauto.
  Qed.

  Lemma compile_gdefs_unique_defs :
    forall src id gd1 gd2
      (NOREPET : Coqlib.list_norepet (List.map fst (compile_gdefs src)))
      (IN1: In (id, gd1) (compile_gdefs src))
      (IN2: In (id, gd2) (compile_gdefs src)),
      gd1 = gd2.
  Proof. i. eapply norepet_unique; eauto. Qed.

End DECOMP.



Section SOLVEID.

  Context `{builtins: builtinsTy}.

  Lemma compile_gdefs_preserves_names :
    forall src,
      <<NAMES:
        List.map s2p
          ((name1 init_g0) ++ (name1 syscalls) ++
           (name1 src.(ext_funsL)) ++ src.(ext_varsL) ++ (name2 src.(prog_funsL)) ++ (name1 src.(prog_varsL)))
        =
        name1 (compile_gdefs src)>>.
  Proof.
    i. unfold compile_gdefs. red. unfold name1. repeat rewrite map_app. repeat f_equal.
    - Local Transparent init_g. Local Transparent init_g0.
      unfold init_g. rewrite ! List.map_map. apply List.map_ext. i. destruct a; ss.
      Local Opaque init_g0. Local Opaque init_g.
    - sym. rewrite List.map_map. apply ext_funs_names.
    - sym. apply ext_vars_names.
    - sym. unfold name2. rewrite List.map_map. apply int_funs_names.
    - sym. rewrite List.map_map. apply int_vars_names.
  Qed.

  Lemma unique_gdefs_unique_name :
    forall src
      (NOREPET : Coqlib.list_norepet (name1 (compile_gdefs src))),
      <<NOREPET: Coqlib.list_norepet ((name1 src.(ext_funsL)) ++ src.(ext_varsL) ++
                                      (name2 src.(prog_funsL)) ++ (name1 src.(prog_varsL)))>>.
  Proof.
    i. rewrite <- compile_gdefs_preserves_names in NOREPET. repeat (rewrite map_app in NOREPET).
    do 2 apply Coqlib.list_norepet_append_right in NOREPET. red.
    rewrite NoDup_norepeat in *.
    repeat (rewrite <- map_app in NOREPET). apply NoDup_map_inv in NOREPET. ss.
  Qed.

  Lemma malloc_unique :
    forall src (NOREPET : Coqlib.list_norepet (List.map fst (compile_gdefs src))),
      ~ In ("malloc") (name1 bts) /\
      ~ In (s2p "malloc") (name1 (c_sys ++ (compile_eFuns (ext_funsL src)) ++ (compile_eVars (ext_varsL src) ++
                                           (compile_iFuns (prog_funsL src)) ++ (compile_iVars (prog_varsL src))))).
  Proof.
    Local Transparent init_g. Local Transparent init_g0.
    i. split.
    { unfold compile_gdefs in NOREPET. rewrite map_app in NOREPET. apply Coqlib.list_norepet_app in NOREPET. des.
      clear NOREPET0 NOREPET1. unfold init_g in NOREPET. unfold init_g0 in NOREPET.
      repeat rewrite map_app in NOREPET. apply Coqlib.list_norepet_app in NOREPET. des.
      unfold Coqlib.list_disjoint in NOREPET1. ii. hexploit NOREPET1.
      { instantiate (1:= s2p "malloc"). rewrite List.map_map. apply (in_map s2p) in H. unfold name1 in H.
        rewrite List.map_map in H. ss.
        match goal with
        | [H: In _ ?ff |- In _ ?gg ] => replace gg with ff end; eauto.
        apply map_ext. i. destruct a. ss. }
      { instantiate (1:= s2p "malloc"). ss. eauto. }
      ii. apply H0; ss. }

    unfold compile_gdefs in NOREPET.
    unfold init_g in NOREPET. unfold init_g0 in NOREPET. ss.
    rewrite map_app in NOREPET. rewrite List.map_map in NOREPET. rewrite map_app in NOREPET. ss.
    apply Coqlib.list_norepet_app in NOREPET. des; ss. unfold Coqlib.list_disjoint in NOREPET1. ii.
    hexploit NOREPET1.
    { instantiate (1:= s2p "malloc"). rewrite in_app_iff. right; ss. left; ss. }
    { eapply H. }
    ii. apply H0. ss.
    Local Opaque init_g0. Local Opaque init_g.
  Qed.

  Lemma free_unique :
    forall src (NOREPET : Coqlib.list_norepet (List.map fst (compile_gdefs src))),
      ~ In ("free") (name1 bts) /\
      ~ In (s2p "free") (name1 (c_sys ++ (compile_eFuns (ext_funsL src)) ++ (compile_eVars (ext_varsL src) ++
                                         (compile_iFuns (prog_funsL src)) ++ (compile_iVars (prog_varsL src))))).
  Proof.
    Local Transparent init_g. Local Transparent init_g0.
    i. split.
    { unfold compile_gdefs in NOREPET. rewrite map_app in NOREPET. apply Coqlib.list_norepet_app in NOREPET. des.
      clear NOREPET0 NOREPET1. unfold init_g in NOREPET. unfold init_g0 in NOREPET.
      repeat rewrite map_app in NOREPET. apply Coqlib.list_norepet_app in NOREPET. des.
      unfold Coqlib.list_disjoint in NOREPET1. ii. hexploit NOREPET1.
      { instantiate (1:= s2p "free"). rewrite List.map_map. apply (in_map s2p) in H. unfold name1 in H.
        rewrite List.map_map in H. ss.
        match goal with
        | [H: In _ ?ff |- In _ ?gg ] => replace gg with ff end; eauto.
        apply map_ext. i. destruct a. ss. }
      { instantiate (1:= s2p "free"). ss. eauto. }
      ii. apply H0; ss. }

    unfold compile_gdefs in NOREPET.
    unfold init_g in NOREPET. unfold init_g0 in NOREPET. ss.
    rewrite map_app in NOREPET. rewrite List.map_map in NOREPET. rewrite map_app in NOREPET. ss.
    apply Coqlib.list_norepet_app in NOREPET. des; ss. unfold Coqlib.list_disjoint in NOREPET1. ii.
    hexploit NOREPET1.
    { instantiate (1:= s2p "free"). rewrite in_app_iff. right; ss; eauto. }
    { eapply H. }
    ii. apply H0. ss.
    Local Opaque init_g0. Local Opaque init_g.
  Qed.

  Lemma init_g_unique :
    forall src id
      (NOREPET : Coqlib.list_norepet (List.map fst (compile_gdefs src)))
      (BTS: In id (name1 init_g)),
      ~ In id (name1 (c_sys ++ (compile_eFuns (ext_funsL src)) ++ (compile_eVars (ext_varsL src) ++
                               (compile_iFuns (prog_funsL src)) ++ (compile_iVars (prog_varsL src))))).
  Proof.
    ii. unfold compile_gdefs in NOREPET.
    rewrite map_app in NOREPET. apply Coqlib.list_norepet_app in NOREPET. des.
    unfold Coqlib.list_disjoint in NOREPET1. hexploit NOREPET1; eauto.
  Qed.

  Lemma init_g_unique_def :
    forall src id fd1 fd2
      (NOREPET : Coqlib.list_norepet (List.map fst (compile_gdefs src)))
      (IN1: In (id, fd1) init_g)
      (IN2: In (id, fd2) init_g),
      fd1 = fd2.
  Proof.
    ii. unfold compile_gdefs in NOREPET.
    rewrite map_app in NOREPET. apply Coqlib.list_norepet_app in NOREPET. des.
    clear NOREPET0 NOREPET1. eapply norepet_unique; eauto.
  Qed.

  Lemma syscalls_unique :
    forall src id
      (NOREPET : Coqlib.list_norepet (List.map fst (compile_gdefs src)))
      (SYS: In id (name1 c_sys)),
      ~ In id (name1 (init_g ++ (compile_eFuns (ext_funsL src)) ++ (compile_eVars (ext_varsL src) ++
                                (compile_iFuns (prog_funsL src)) ++ (compile_iVars (prog_varsL src))))).
  Proof.
    ii. unfold compile_gdefs in NOREPET.
    rewrite map_app in NOREPET. apply Coqlib.list_norepet_app in NOREPET. des.
    unfold name1 in H. rewrite map_app in H. apply in_app_or in H. des.
    { unfold Coqlib.list_disjoint in NOREPET1. hexploit NOREPET1; eauto.
      rewrite map_app. apply in_or_app. left; auto. }
    clear NOREPET NOREPET1.
    rewrite map_app in NOREPET0. apply Coqlib.list_norepet_app in NOREPET0. des. clear NOREPET0 NOREPET1.
    unfold Coqlib.list_disjoint in NOREPET2. ii. hexploit NOREPET2; eauto.
  Qed.

  Lemma l_efs_prop :
    forall src1 src2 name sig
      (NOREPET1 : Coqlib.list_norepet (name1 (ext_funsL src1) ++ ext_varsL src1 ++
                                       name2 (prog_funsL src1) ++ name1 (prog_varsL src1)))
      (NOREPET2 : Coqlib.list_norepet (name1 (ext_funsL src2) ++ ext_varsL src2 ++
                                       name2 (prog_funsL src2) ++ name1 (prog_varsL src2)))
      (IN1 : In (name, sig) (ext_funsL src1))
      (IN2 : In (name, sig) (ext_funsL src2)),
      <<INLEFS: In (compile_eFun (name, sig)) (compile_eFuns (l_efs src1 src2))>>.
  Proof.
    ii. red. unfold l_efs, compile_eFuns. apply in_map. apply filter_In. split.
    2:{ unfold name2, l_pfs. apply negb_true_iff. apply sumbool_to_bool_is_false. ii. ss.
        rewrite map_app in H. apply in_app_iff in H. des.
        - depgen src1. clear; i. apply (in_map fst) in IN1. ss. rewrite Coqlib.list_norepet_app in NOREPET1. des.
          clear NOREPET1 NOREPET0. unfold Coqlib.list_disjoint in NOREPET2. hexploit NOREPET2.
          { eauto. }
          { rewrite in_app_iff. right. rewrite in_app_iff; left. eauto. }
          ii. clarify.
        - depgen src2. clear; i. apply (in_map fst) in IN2. ss. rewrite Coqlib.list_norepet_app in NOREPET2. des.
          clear NOREPET2 NOREPET0. unfold Coqlib.list_disjoint in NOREPET1. hexploit NOREPET1.
          { eauto. }
          { rewrite in_app_iff. right. rewrite in_app_iff; left. eauto. }
          ii. clarify.
    }
    set (ef:=(name, sig)) in *.
    rewrite nodup_In. apply in_app_iff. auto.
  Qed.

  Lemma l_evs_prop :
    forall src1 src2 name
      (NOREPET1 : Coqlib.list_norepet (name1 (ext_funsL src1) ++ ext_varsL src1 ++
                                       name2 (prog_funsL src1) ++ name1 (prog_varsL src1)))
      (NOREPET2 : Coqlib.list_norepet (name1 (ext_funsL src2) ++ ext_varsL src2 ++
                                       name2 (prog_funsL src2) ++ name1 (prog_varsL src2)))
      (IN1 : In name (ext_varsL src1))
      (IN2 : In name (ext_varsL src2)),
      <<INLEVS: In (compile_eVar name) (compile_eVars (l_evs src1 src2))>>.
  Proof.
    ii. red. unfold l_evs, compile_eVars. apply in_map. apply filter_In. split.
    2:{ unfold name1, l_pvs. apply negb_true_iff. apply sumbool_to_bool_is_false. ii. ss.
        rewrite map_app in H. apply in_app_iff in H. des.
        - depgen src1; clear; i.
          rewrite Coqlib.list_norepet_app in NOREPET1. des. clear NOREPET1 NOREPET2.
          rewrite Coqlib.list_norepet_app in NOREPET0. des. clear NOREPET1 NOREPET0.
          unfold Coqlib.list_disjoint in NOREPET2. hexploit NOREPET2.
          { eapply IN1. }
          { rewrite in_app_iff; right. eauto. }
          ii; clarify.
        - depgen src2; clear; i.
          rewrite Coqlib.list_norepet_app in NOREPET2. des. clear NOREPET1 NOREPET2.
          rewrite Coqlib.list_norepet_app in NOREPET0. des. clear NOREPET1 NOREPET0.
          unfold Coqlib.list_disjoint in NOREPET2. hexploit NOREPET2.
          { eapply IN2. }
          { rewrite in_app_iff; right. eauto. }
          ii; clarify.
    }
    rewrite nodup_In. apply in_app_iff. auto.
  Qed.

End SOLVEID.



Section UNLINK.

  Context `{builtins: builtinsTy}.

  Lemma unlink_l_evs
        vd src1 src2
        (INL: In vd (l_evs src1 src2))
  :
    (<<IN1: In vd (ext_varsL src1)>>) \/ (<<IN2: In vd (ext_varsL src2)>>).
  Proof.
    unfold l_evs in INL. apply filter_In in INL. des. apply nodup_In in INL. apply in_app_iff in INL; auto.
  Qed.

  Lemma unlink_l_efs
        fd src1 src2
        (INL: In fd (l_efs src1 src2))
  :
    (<<IN1: In fd (ext_funsL src1)>>) \/ (<<IN2: In fd (ext_funsL src2)>>).
  Proof.
    unfold l_efs in INL. apply filter_In in INL. des. apply nodup_In in INL. apply in_app_iff in INL; auto.
  Qed.

  Lemma unlink_l_pvs
        vd src1 src2
        (INL: In vd (l_pvs src1 src2))
  :
    (<<IN1: In vd (prog_varsL src1)>>) \/ (<<IN2: In vd (prog_varsL src2)>>).
  Proof.
    unfold l_pvs in INL. apply in_app_iff in INL; auto.
  Qed.

  Lemma unlink_l_pfs
        fd src1 src2
        (INL: In fd (l_pfs src1 src2))
  :
    (<<IN1: In fd (prog_funsL src1)>>) \/ (<<IN2: In fd (prog_funsL src2)>>).
  Proof.
    unfold l_pfs in INL. apply in_app_iff in INL; auto.
  Qed.

End UNLINK.



Section LINKPROPS.

  Context `{builtins: builtinsTy}.

  Lemma link_imp_cond1_comm :
    forall src1 src2,
      <<LC1: link_imp_cond1 src1 src2 = true -> link_imp_cond1 src2 src1 = true>>.
  Proof.
    ii. apply link_imp_cond1_prop in H. des. unfold link_imp_cond1. bsimpl. repeat (try split).
    all: apply sumbool_to_bool_is_true.
    - depgen EV2; clear; i. unfold l_pfs in *. unfold name2 in *. rewrite map_app in *.
      eapply Cminorgenproof.permutation_norepet. 2:{ eauto. }
      apply Permutation_app_head. apply Permutation_app_comm.
    - depgen EV1; clear; i. unfold l_pfs in *. unfold name2 in *. rewrite map_app in *.
      eapply Cminorgenproof.permutation_norepet. 2:{ eauto. }
      apply Permutation_app_head. apply Permutation_app_comm.
    - depgen EF0; clear; i. unfold l_pvs in *. unfold name1 in *. rewrite map_app in *.
      eapply Cminorgenproof.permutation_norepet. 2:{ eauto. }
      apply Permutation_app_head. apply Permutation_app_comm.
    - depgen EF1; clear; i. unfold l_pvs in *. unfold name1 in *. rewrite map_app in *.
      eapply Cminorgenproof.permutation_norepet. 2:{ eauto. }
      apply Permutation_app_head. apply Permutation_app_comm.
    - depgen EVF2; clear; i. auto.
    - depgen EVF1; clear; i. auto.
  Qed.

  Lemma link_imp_cond2_comm :
    forall src1 src2,
      <<LC2: link_imp_cond2 src1 src2 = true -> link_imp_cond2 src2 src1 = true>>.
  Proof.
    ii. unfold link_imp_cond2 in *. eapply _link_imp_cond2_prop_perm.
    2:{ eapply H. }
    apply Permutation_app_comm.
  Qed.

  Lemma link_then_unique_ids
        src1 src2 srcl
        (LINK : link_imp src1 src2 = Some srcl)
    :
      <<UIDS : Coqlib.list_norepet (name1 (compile_gdefs srcl))>>.
  Proof.
    unfold link_imp in LINK. des_ifs. bsimpl. des.
    rewrite <- compile_gdefs_preserves_names. ss. apply link_imp_cond3_prop in Heq0.
    apply Coqlib.list_map_norepet; eauto.
    i. ii. apply s2p_inj in H2. ss.
  Qed.

  Lemma link_then_exists_gd
        src1 src2 srcl id gd1 gd2
        (NOREPET1 : Coqlib.list_norepet (List.map fst (compile_gdefs src1)))
        (NOREPET2 : Coqlib.list_norepet (List.map fst (compile_gdefs src2)))
        (LINKSRC : link_imp src1 src2 = Some srcl)
        (IN1 : In (id, gd1) (compile_gdefs src1))
        (IN2 : In (id, gd2) (compile_gdefs src2))
    :
      exists gdl, (<<LINK: link gd1 gd2 = Some gdl>>) /\ (<<INL: In (id, gdl) (compile_gdefs srcl)>>).
  Proof.
    Local Transparent Linker_def. Local Transparent Linker_fundef.
    Local Transparent Linker_vardef. Local Transparent Linker_varinit.
    hexploit link_then_unique_ids; eauto. i. des. rename H into NOREPETL.
    hexploit (decomp_gdefs_split src1 id gd1 IN1). i. rename H into SRC1.
    hexploit (decomp_gdefs_split src2 id gd2 IN2). i. rename H into SRC2.

    (* init_g *)
    destruct SRC1 as [SRC1 | SRC1].
    { destruct SRC1 as [ING SRC1]. eapply init_g_unique in ING. 2:{ eapply NOREPET2. }
      destruct SRC2 as [SRC2 | SRC2].
      2:{ unfold name1 in ING. repeat rewrite map_app in ING. exfalso. apply ING. clear ING.
          repeat rewrite in_app_iff. clear SRC1. des; eauto.
          - left. destruct fd; ss; clarify. unfold c_sys. rewrite List.map_map.
            apply (in_map (fst ∘ compile_eFun)) in SYS0. ss.
          - right; left. destruct fd; ss; clarify. unfold compile_eFuns. rewrite List.map_map.
            apply (in_map (fst ∘ compile_eFun)) in EFS0. ss.
          - do 2 right; left. unfold compile_eVar in *. ss; clarify. unfold compile_eVars. rewrite List.map_map.
            apply (in_map (fst ∘ compile_eVar)) in EVS0. ss.
          - do 3 right; left. destruct fd as [mn [fn ff]]; ss; clarify. unfold compile_iFuns. rewrite List.map_map.
            apply (in_map (fst ∘ compile_iFun)) in IFS0. ss.
          - do 4 right. destruct vd; ss; clarify. unfold compile_iVars. rewrite List.map_map.
            apply (in_map (fst ∘ compile_iVar)) in IVS0. ss.
      }
      clear ING. destruct SRC2 as [ING SRC2]. clear ING.
      destruct SRC1 as [SRC1 | SRC1].
      { destruct SRC2 as [SRC2 | SRC2].
        { des. ss; clarify. destruct fd0; destruct fd; ss; clarify. apply s2p_inj in SRC2; clarify.
          assert (EF: exists ef, g = Gfun (External ef)).
          { unfold bts in SRC5. apply Coqlib.list_in_map_inv in SRC5. des. destruct x. ss; clarify. exists e; auto. }
          apply in_bts_in_init_g in SRC5; apply in_bts_in_init_g in SRC3.
          hexploit init_g_unique_def.
          eapply NOREPET1. eapply SRC5. eapply SRC3. i. ss; clarify. exists g0; split; eauto.
          2:{ eapply in_compile_gdefs_init_g; eauto. }
          des. clarify. ss. des_ifs. }
        des.
        - hexploit malloc_unique; eauto. i. des. destruct fd; ss; clarify. apply s2p_inj in MALLOC. clarify.
          apply (in_map fst) in SRC3. ss.
        - hexploit free_unique; eauto. i. des. destruct fd; ss; clarify. apply s2p_inj in FREE. clarify.
          apply (in_map fst) in SRC3. ss.
      }
      destruct SRC2 as [SRC2 | SRC2].
      { des.
        - hexploit malloc_unique; eauto. i. des. destruct fd; ss; clarify. apply s2p_inj in SRC2. clarify.
          apply (in_map fst) in SRC3. ss.
        - hexploit free_unique; eauto. i. des. destruct fd; ss; clarify. apply s2p_inj in SRC2. clarify.
          apply (in_map fst) in SRC3. ss.
      }
      des; ss; clarify.
      - exists (Gfun (External EF_malloc)). split; eauto. apply has_malloc.
      - apply s2p_inj in MALLOC; clarify.
      - apply s2p_inj in FREE; clarify.
      - exists (Gfun (External EF_free)). split; eauto. apply has_free.
    }
    destruct SRC2 as [SRC2 | SRC2].
    { destruct SRC2 as [ING SRC2]. eapply init_g_unique in ING. 2:{ eapply NOREPET1. }
      unfold name1 in ING. repeat rewrite map_app in ING. exfalso. apply ING. clear ING.
      repeat rewrite in_app_iff. clear SRC2. des; eauto.
      - left. destruct fd; ss; clarify. unfold c_sys. rewrite List.map_map.
        apply (in_map (fst ∘ compile_eFun)) in SYS0. ss.
      - right; left. destruct fd; ss; clarify. unfold compile_eFuns. rewrite List.map_map.
        apply (in_map (fst ∘ compile_eFun)) in EFS0. ss.
      - do 2 right; left. unfold compile_eVar in *. ss; clarify. unfold compile_eVars. rewrite List.map_map.
        apply (in_map (fst ∘ compile_eVar)) in EVS0. ss.
      - do 3 right; left. destruct fd as [mn [fn ff]]; ss; clarify. unfold compile_iFuns. rewrite List.map_map.
        apply (in_map (fst ∘ compile_iFun)) in IFS0. ss.
      - do 4 right. destruct vd; ss; clarify. unfold compile_iVars. rewrite List.map_map.
        apply (in_map (fst ∘ compile_iVar)) in IVS0. ss.
    }

    (* syscalls *)
    destruct SRC1 as [SRC1 | SRC1].
    { clear SRC2. des. clarify. unfold compile_gdefs in IN2.
      apply in_app_or in IN2. des.
      { apply (in_map (fst ∘ compile_eFun)) in SRC0. eapply syscalls_unique in NOREPET2.
        2:{ unfold c_sys. eapply SRC0. }
        clarify. exfalso. apply NOREPET2; clear NOREPET2. apply (in_map fst) in IN2. cbn. rewrite SRC1. ss. unfold name1.
        rewrite map_app. rewrite in_app_iff. left; auto. }
      apply in_app_or in IN2. des.
      2:{ apply (in_map (fst ∘ compile_eFun)) in SRC0. eapply syscalls_unique in NOREPET2.
          2:{ unfold c_sys. eapply SRC0. }
          clarify. exfalso. apply NOREPET2; clear NOREPET2. apply (in_map fst) in IN2. cbn. rewrite SRC1. ss. unfold name1.
          rewrite map_app. rewrite in_app_iff. right; auto. }
      apply decomp_c_sys in IN2. des. ss; clarify. unfold compile_eFun in *. destruct fd; destruct fd0. ss; clarify.
      apply s2p_inj in H1. clarify.
      eapply (in_compile_gdefs_c_sys srcl) in IN0.
      eapply (in_compile_gdefs_c_sys srcl) in SRC0.
      unfold compile_eFun in *. hexploit (compile_gdefs_unique_defs srcl _ _ _ NOREPETL IN0 SRC0); eauto.
      i. eexists. split.
      2:{ eapply IN0. }
      rewrite H. red. clear. ss. des_ifs.
    }
    destruct SRC2 as [SRC2 | SRC2].
    { clear SRC1. des. clarify. unfold compile_gdefs in IN1.
      apply in_app_or in IN1. des.
      { apply (in_map (fst ∘ compile_eFun)) in SRC0. eapply syscalls_unique in NOREPET1.
        2:{ unfold c_sys. eapply SRC0. }
        clarify. exfalso. apply NOREPET1; clear NOREPET1. apply (in_map fst) in IN1. cbn. rewrite SRC2. ss. unfold name1.
        rewrite map_app. rewrite in_app_iff. left; auto. }
      apply in_app_or in IN1. des.
      2:{ apply (in_map (fst ∘ compile_eFun)) in SRC0. eapply syscalls_unique in NOREPET1.
          2:{ unfold c_sys. eapply SRC0. }
          clarify. exfalso. apply NOREPET1; clear NOREPET1. apply (in_map fst) in IN1. cbn. rewrite SRC2. ss. unfold name1.
          rewrite map_app. rewrite in_app_iff. right; auto. }
      apply decomp_c_sys in IN1. des. ss; clarify. unfold compile_eFun in *. destruct fd; destruct fd0. ss; clarify.
      apply s2p_inj in H1. clarify.
      eapply (in_compile_gdefs_c_sys srcl) in IN0.
      eapply (in_compile_gdefs_c_sys srcl) in SRC0.
      unfold compile_eFun in *. hexploit (compile_gdefs_unique_defs srcl _ _ _ NOREPETL IN0 SRC0); eauto.
      i. eexists. split.
      2:{ eapply IN0. }
      rewrite H. red. clear. ss. des_ifs.
    }

    (* symbol resolution *)
    clear IN1 IN2. unfold link_imp in LINKSRC. des_ifs_safe. bsimpl. destruct Heq. destruct H.
    rename H into LC1, H1 into LC2, H0 into LC3.
    des.

    - (* ef/ef *)
      apply link_imp_cond2_prop in LC2.
      assert (snd fd0 = snd fd).
      { eapply LC2. repeat split.
        - rewrite in_app_iff. left; auto.
        - rewrite in_app_iff. right; auto.
        - unfold compile_eFun in *; ss; clarify. destruct fd0; destruct fd; ss; clarify. apply s2p_inj in H1; ss.
      }
      unfold compile_eFun in *; ss; clarify. destruct fd0; destruct fd; ss; clarify. apply s2p_inj in H1; ss; clarify.
      exists (snd (compile_eFun (s0, n0))). unfold compile_eFun. split.
      { des_ifs. }
      red. unfold compile_gdefs. ss. do 2 (apply in_app_iff; right). apply in_app_iff; left.
      apply unique_gdefs_unique_name in NOREPET1. apply unique_gdefs_unique_name in NOREPET2.
      eapply l_efs_prop; eauto.

    - (* ev/ef *)
      clear NOREPETL. exfalso. apply link_imp_cond1_prop in LC1. des.
      apply Coqlib.list_norepet_app in EVF1. des. unfold Coqlib.list_disjoint in EVF3.
      hexploit EVF3; eauto. unfold compile_eVar in *. ss; clarify. unfold compile_eFun in *. ss; clarify.
      destruct fd; ss; clarify. apply s2p_inj in H1. clarify. apply (in_map fst) in EFS0. ss.

    - (* if/ef *)
      exists (snd (compile_iFun fd0)). split.
      { destruct fd0 as [mn [fn impf]]. unfold compile_iFun in IFS. clarify; ss.
        destruct fd as [efn sig]. unfold compile_eFun in EFS. clarify; ss. }
      red. unfold compile_gdefs. ss. do 4 (rewrite in_app_iff; right). rewrite in_app_iff; left.
      unfold l_pfs. unfold compile_iFuns. rewrite map_app. rewrite in_app_iff; left.
      apply (in_map compile_iFun) in IFS0. rewrite IFS in *. ss.

    - (* iv/ef *)
      clear NOREPETL. exfalso. apply link_imp_cond1_prop in LC1. des.
      apply Coqlib.list_norepet_app in EF0. des. unfold Coqlib.list_disjoint in EF3.
      unfold name1 in EF3. apply (in_map fst) in EFS0. apply (in_map fst) in IVS0.
      hexploit EF3; eauto. unfold l_pvs. rewrite map_app. apply in_app_iff; left.
      destruct vd; destruct fd; ss. clarify. apply s2p_inj in H1; clarify; auto.

    - (* ef/ev *)
      clear NOREPETL. exfalso. apply link_imp_cond1_prop in LC1. des.
      apply Coqlib.list_norepet_app in EVF2. des. unfold Coqlib.list_disjoint in EVF3.
      hexploit EVF3; eauto. unfold compile_eVar in *. ss; clarify. unfold compile_eFun in *. ss; clarify.
      destruct fd; ss; clarify. apply s2p_inj in H1. clarify. apply (in_map fst) in EFS0. ss.

    - (* ev/ev *)
      exists (snd (compile_eVar vd0)). split.
      { unfold compile_eVar in *; ss; clarify. }
      red. unfold compile_gdefs; ss. do 3 (apply in_app_iff; right). apply in_app_iff; left.
      unfold compile_eVar in *; ss; clarify. apply s2p_inj in H1; clarify.
      apply unique_gdefs_unique_name in NOREPET1. apply unique_gdefs_unique_name in NOREPET2.
      eapply l_evs_prop; eauto.

    - (* if/ev *)
      clear NOREPETL. exfalso. apply link_imp_cond1_prop in LC1. des.
      apply Coqlib.list_norepet_app in EV2. des. unfold Coqlib.list_disjoint in EV3.
      unfold name2 in EV3. apply (in_map (fst ∘ snd)) in IFS0.
      hexploit EV3; eauto. unfold l_pfs. rewrite map_app. apply in_app_iff; left.
      destruct fd. destruct p. unfold compile_eVar in *; ss; clarify. apply s2p_inj in H1; clarify; auto.

    - (* iv/ev *)
      exists (snd (compile_iVar vd0)). split.
      { destruct vd0. unfold compile_eVar in *. ss; clarify. }
      red. unfold compile_gdefs; ss. do 5 (apply in_app_iff; right). unfold l_pvs.
      unfold compile_iVars. rewrite map_app. apply in_app_iff; left.
      apply (in_map compile_iVar) in IVS0. rewrite IVS in *. ss.

    - (* ef/if *)
      exists (snd (compile_iFun fd)). split.
      { destruct fd as [mn [fn impf]]. unfold compile_iFun in *. clarify; ss.
        destruct fd0 as [efn sig]. unfold compile_eFun in *. clarify; ss. }
      red. unfold compile_gdefs. ss. do 4 (rewrite in_app_iff; right). rewrite in_app_iff; left.
      unfold l_pfs. unfold compile_iFuns. rewrite map_app. rewrite in_app_iff; right.
      apply (in_map compile_iFun) in IFS0. rewrite IFS in *. ss.

    - (* ev/if *)
      clear NOREPETL. exfalso. apply link_imp_cond1_prop in LC1. des.
      apply Coqlib.list_norepet_app in EV1. des. unfold Coqlib.list_disjoint in EV3.
      unfold name2 in EV3. apply (in_map (fst ∘ snd)) in IFS0.
      hexploit EV3; eauto. unfold l_pfs. rewrite map_app. apply in_app_iff; right.
      destruct fd. destruct p. unfold compile_eVar in *; ss; clarify. apply s2p_inj in H1; clarify; auto.

    - (* if/if *)
      clear NOREPETL. exfalso. apply link_imp_cond3_ints in LC3. des. unfold Coqlib.list_disjoint in IFIF.
      unfold name2 in *. apply (in_map (fst ∘ snd)) in IFS2. apply (in_map (fst ∘ snd)) in IFS0.
      hexploit IFIF; eauto. ii. destruct fd0 as [mn0 [fn0 ff0]]; destruct fd as [mn [fn ff]]. ss; clarify.
      apply s2p_inj in H2; clarify.

    - (* iv/if *)
      clear NOREPETL. exfalso. apply link_imp_cond3_ints in LC3. des. unfold Coqlib.list_disjoint in IVIF.
      unfold name2 in *. unfold name1 in *. apply (in_map (fst ∘ snd)) in IFS0. apply (in_map fst) in IVS0.
      hexploit IVIF; eauto. ii. destruct vd; destruct fd as [mn [fn ff]]. ss; clarify.
      apply s2p_inj in H2; clarify.

    - (* ef/iv *)
      clear NOREPETL. exfalso. apply link_imp_cond1_prop in LC1. des.
      apply Coqlib.list_norepet_app in EF1. des. unfold Coqlib.list_disjoint in EF3.
      unfold name1 in EF3. apply (in_map fst) in EFS0. apply (in_map fst) in IVS0.
      hexploit EF3; eauto. unfold l_pvs. rewrite map_app. apply in_app_iff; right.
      destruct vd; destruct fd; ss. clarify. apply s2p_inj in H1; clarify; auto.

    - (* ev/iv *)
      exists (snd (compile_iVar vd)). split.
      { destruct vd. unfold compile_eVar in *. ss; clarify. }
      red. unfold compile_gdefs; ss. do 5 (apply in_app_iff; right). unfold l_pvs.
      unfold compile_iVars. rewrite map_app. apply in_app_iff; right.
      apply (in_map compile_iVar) in IVS0. rewrite IVS in *. ss.

    - (* if/iv *)
      clear NOREPETL. exfalso. apply link_imp_cond3_ints in LC3. des. unfold Coqlib.list_disjoint in IFIV.
      unfold name2 in *. unfold name1 in *. apply (in_map (fst ∘ snd)) in IFS0. apply (in_map fst) in IVS0.
      hexploit IFIV; eauto. ii. destruct vd; destruct fd as [mn [fn ff]]. ss; clarify.
      apply s2p_inj in H2; clarify.

    - (* iv/iv *)
      clear NOREPETL. exfalso. apply link_imp_cond3_ints in LC3. des. unfold Coqlib.list_disjoint in IVIV.
      unfold name1 in *. apply (in_map fst) in IVS2. apply (in_map fst) in IVS0.
      hexploit IVIV; eauto. ii. destruct vd0 as [vn0 vv0]; destruct vd as [vn vv]. ss; clarify.
      apply s2p_inj in H2; clarify.

      Local Opaque Linker_varinit. Local Opaque Linker_vardef.
      Local Opaque Linker_fundef. Local Opaque Linker_def.
  Qed.

  Lemma in_tgtl_then_in_some
        src1 src2 srcl id gd
        (LINKSRC : link_imp src1 src2 = Some srcl)
        (INL : In (id, gd) (compile_gdefs srcl))
    :
      (<<IN1: In (id, gd) (compile_gdefs src1)>>) \/ (<<BK: In (id, gd) (compile_gdefs src2)>>).
  Proof.
    unfold link_imp in LINKSRC. des_ifs; ss. apply decomp_gdefs in INL; des; ss; clarify.
    - left. red. eapply has_bts. destruct fd; eauto.
    - left. red. eapply has_malloc.
    - left. red. eapply has_free.
    - left. red. rewrite <- SYS. apply in_compile_gdefs_c_sys. ss.
    - apply unlink_l_efs in EFS0. des.
      + left. rewrite <- EFS. apply in_compile_gdefs_efuns. ss.
      + right. rewrite <- EFS. apply in_compile_gdefs_efuns. ss.
    - apply unlink_l_evs in EVS0. des.
      + left. rewrite <- EVS. apply in_compile_gdefs_evars. ss.
      + right. rewrite <- EVS. apply in_compile_gdefs_evars. ss.
    - apply unlink_l_pfs in IFS0. des.
      + left. rewrite <- IFS. apply in_compile_gdefs_ifuns. ss.
      + right. rewrite <- IFS. apply in_compile_gdefs_ifuns. ss.
    - apply unlink_l_pvs in IVS0. des.
      + left. rewrite <- IVS. apply in_compile_gdefs_ivars. ss.
      + right. rewrite <- IVS. apply in_compile_gdefs_ivars. ss.
  Qed.

  Lemma in_left_in_link
        src1 src2 srcl id gd
        (LINKSRC : link_imp src1 src2 = Some srcl)
        (NOREPET1 : Coqlib.list_norepet (List.map fst (compile_gdefs src1)))
        (NOREPET2 : Coqlib.list_norepet (List.map fst (compile_gdefs src2)))
        (IN1: In (id, gd) (compile_gdefs src1))
        (NOTIN2: ~ In id (List.map fst (compile_gdefs src2)))
    :
      In (id, gd) (compile_gdefs srcl).
  Proof.
    unfold link_imp in LINKSRC. des_ifs. clear Heq.
    apply decomp_gdefs in IN1. des; ss; clarify.
    - apply has_bts. destruct fd; ss.
    - apply has_malloc.
    - apply has_free.
    - rewrite <- SYS. eapply in_compile_gdefs_c_sys; eauto.
    - rewrite <- EFS. eapply in_compile_gdefs_efuns. ss. unfold l_efs.
      rewrite filter_In. split.
      { rewrite nodup_In. rewrite in_app_iff. left; auto. }
      apply negb_true_iff. apply sumbool_to_bool_is_false. ii. apply NOTIN2; clear NOTIN2.
      unfold l_pfs in *. unfold name2 in *. rewrite map_app in H. rewrite in_app_iff in H. des.
      + depgen src1. depgen id. clear; i.
        apply unique_gdefs_unique_name in NOREPET1. des.
        apply Coqlib.list_norepet_app in NOREPET1. des. clear NOREPET1 NOREPET0.
        unfold Coqlib.list_disjoint in NOREPET2.
        destruct fd as [name sig]; ss; clarify. apply (in_map fst) in EFS0; ss.
        hexploit NOREPET2; eauto.
        { apply in_app_iff; right. apply in_app_iff; left. eapply H. }
        ii; clarify.
      + depgen src2. depgen id. clear; i.
        apply Coqlib.list_in_map_inv in H. des. apply in_compile_gdefs_ifuns in H0. des.
        apply (in_map fst) in H0. destruct fd; ss; clarify.
        destruct x as [mn [fn ff]]; ss; clarify.
    - rewrite <- EVS. eapply in_compile_gdefs_evars. ss. unfold l_evs.
      rewrite filter_In. split.
      { rewrite nodup_In. rewrite in_app_iff. left; auto. }
      apply negb_true_iff. apply sumbool_to_bool_is_false. ii. apply NOTIN2; clear NOTIN2.
      unfold l_pvs in *. unfold name1 in *. rewrite map_app in H. rewrite in_app_iff in H. des.
      + depgen src1. depgen id. clear; i.
        apply unique_gdefs_unique_name in NOREPET1. des.
        apply Coqlib.list_norepet_app in NOREPET1. des. clear NOREPET1 NOREPET2.
        apply Coqlib.list_norepet_app in NOREPET0. des. clear NOREPET1 NOREPET0.
        unfold Coqlib.list_disjoint in NOREPET2.
        unfold compile_eVar in *; ss; clarify.
        hexploit NOREPET2; eauto.
        { apply in_app_iff; right. eapply H. }
        ii; clarify.
      + depgen src2. depgen id. clear; i.
        apply Coqlib.list_in_map_inv in H. des. apply in_compile_gdefs_ivars in H0. des.
        apply (in_map fst) in H0. unfold compile_eVar in *; ss; clarify.
        destruct x as [vn vv]; ss; clarify.
    - rewrite <- IFS. eapply in_compile_gdefs_ifuns. ss. unfold l_pfs.
      apply in_app_iff. left; auto.
    - rewrite <- IVS. eapply in_compile_gdefs_ivars. ss. unfold l_pvs.
      apply in_app_iff. left; auto.
  Qed.

  Lemma in_right_in_link
        src1 src2 srcl id gd
        (LINKSRC : link_imp src1 src2 = Some srcl)
        (NOREPET1 : Coqlib.list_norepet (List.map fst (compile_gdefs src1)))
        (NOREPET2 : Coqlib.list_norepet (List.map fst (compile_gdefs src2)))
        (IN2: In (id, gd) (compile_gdefs src2))
        (NOTIN1: ~ In id (List.map fst (compile_gdefs src1)))
    :
      In (id, gd) (compile_gdefs srcl).
  Proof.
    unfold link_imp in LINKSRC. des_ifs. clear Heq.
    apply decomp_gdefs in IN2. des; ss; clarify.
    - apply has_bts. destruct fd; ss.
    - apply has_malloc.
    - apply has_free.
    - rewrite <- SYS. eapply in_compile_gdefs_c_sys; eauto.
    - rewrite <- EFS. eapply in_compile_gdefs_efuns. ss. unfold l_efs.
      rewrite filter_In. split.
      { rewrite nodup_In. rewrite in_app_iff. right; auto. }
      apply negb_true_iff. apply sumbool_to_bool_is_false. ii. apply NOTIN1; clear NOTIN1.
      unfold l_pfs in *. unfold name2 in *. rewrite map_app in H. rewrite in_app_iff in H. des.
      + depgen src1. depgen id. clear; i.
        apply Coqlib.list_in_map_inv in H. des. apply in_compile_gdefs_ifuns in H0. des.
        apply (in_map fst) in H0. destruct fd; ss; clarify.
        destruct x as [mn [fn ff]]; ss; clarify.
      + depgen src2. depgen id. clear; i.
        apply unique_gdefs_unique_name in NOREPET2. des.
        apply Coqlib.list_norepet_app in NOREPET2. des. clear NOREPET2 NOREPET0.
        unfold Coqlib.list_disjoint in NOREPET1.
        destruct fd as [name sig]; ss; clarify. apply (in_map fst) in EFS0; ss.
        hexploit NOREPET1; eauto.
        { apply in_app_iff; right. apply in_app_iff; left. eapply H. }
        ii; clarify.
    - rewrite <- EVS. eapply in_compile_gdefs_evars. ss. unfold l_evs.
      rewrite filter_In. split.
      { rewrite nodup_In. rewrite in_app_iff. right; auto. }
      apply negb_true_iff. apply sumbool_to_bool_is_false. ii. apply NOTIN1; clear NOTIN1.
      unfold l_pvs in *. unfold name1 in *. rewrite map_app in H. rewrite in_app_iff in H. des.
      + depgen src1. depgen id. clear; i.
        apply Coqlib.list_in_map_inv in H. des. apply in_compile_gdefs_ivars in H0. des.
        apply (in_map fst) in H0. unfold compile_eVar in *; ss; clarify.
        destruct x as [vn vv]; ss; clarify.
      + depgen src2. depgen id. clear; i.
        apply unique_gdefs_unique_name in NOREPET2. des.
        apply Coqlib.list_norepet_app in NOREPET2. des. clear NOREPET1 NOREPET2.
        apply Coqlib.list_norepet_app in NOREPET0. des. clear NOREPET1 NOREPET0.
        unfold Coqlib.list_disjoint in NOREPET2.
        unfold compile_eVar in *; ss; clarify.
        hexploit NOREPET2; eauto.
        { apply in_app_iff; right. eapply H. }
        ii; clarify.
    - rewrite <- IFS. eapply in_compile_gdefs_ifuns. ss. unfold l_pfs.
      apply in_app_iff. right; auto.
    - rewrite <- IVS. eapply in_compile_gdefs_ivars. ss. unfold l_pvs.
      apply in_app_iff. right; auto.
  Qed.

End LINKPROPS.



Section PROOF.

  Import Permutation.

  Context `{builtins: builtinsTy}.

  Definition wf_prog_incl (src: Imp.programL) :=
    <<WFPROG: (incl (name1 src.(defsL)) ((name1 src.(prog_varsL)) ++ (name2 src.(prog_funsL))))>>.

  Definition wf_prog_gvar (src: Imp.programL) :=
    <<WFPROG2 : forall gn gv, In (gn, Sk.Gvar gv) (Sk.sort (defsL src)) -> In (gn, gv) (prog_varsL src)>>.

  Definition wf_prog src := wf_prog_incl src /\ wf_prog_gvar src.

  Lemma lifted_then_wf :
    forall (src: Imp.program), <<WFLIFT: wf_prog (lift src)>>.
  Proof.
    i. unfold lift. split.
    - unfold wf_prog_incl. ss. unfold defs. red. ii. unfold name1, name2 in *.
      rewrite List.map_map; ss.
      apply Coqlib.list_in_map_inv in H. des.
      destruct x; ss; clarify. apply filter_In in H0. des. ss.
      apply (in_map fst) in H0. ss.
      rewrite map_app in H0. rewrite ! List.map_map in H0. rewrite in_app_iff in H0. des; ss.
      + rewrite in_app_iff. right.
        match goal with | [ H0: In _ (List.map ?mf0 _) |- In _ (List.map ?mf1 _) ] => replace mf1 with mf0; eauto end.
        extensionality x. destruct x. ss.
      + rewrite in_app_iff. left.
        match goal with | [ H0: In _ (List.map ?mf0 _) |- In _ (List.map ?mf1 _) ] => replace mf1 with mf0; eauto end.
        extensionality x. destruct x. ss.
    - unfold wf_prog_gvar. ss. red. unfold defs. i. apply Sk.sort_incl_rev in H.
      apply filter_In in H. des. ss.
      apply in_app_or in H. des.
      + apply Coqlib.list_in_map_inv in H. des. destruct x. ss.
      + apply Coqlib.list_in_map_inv in H. des. destruct x. clarify.
  Qed.

  Lemma linked_two_wf :
    forall (src1 src2: Imp.programL) srcl
      (WF1: wf_prog src1)
      (WF2: wf_prog src2)
      (LINKED: link_imp src1 src2 = Some srcl),
      <<WFLINK: wf_prog srcl>>.
  Proof.
    i. unfold wf_prog in *. des. unfold link_imp in LINKED. des_ifs. split.
    - unfold wf_prog_incl in *; ss. unfold l_pvs; unfold l_pfs; unfold l_defsL.
      red. ii. unfold name1, name2 in *. rewrite map_app in H. apply in_app_iff in H. des.
      + apply WF1 in H. apply in_app_iff in H. des.
        * apply in_app_iff. left. rewrite map_app. apply in_app_iff. auto.
        * apply in_app_iff. right. rewrite map_app. apply in_app_iff. auto.
      + apply WF2 in H. apply in_app_iff in H. des.
        * apply in_app_iff. left. rewrite map_app. apply in_app_iff. auto.
        * apply in_app_iff. right. rewrite map_app. apply in_app_iff. auto.
    - unfold wf_prog_gvar in *; ss. ii. apply Sk.sort_incl_rev in H. apply in_or_app. apply in_app_or in H. des.
      + left; apply WF3. apply Sk.sort_incl. auto.
      + right; apply WF0. apply Sk.sort_incl. auto.
  Qed.

  Lemma linked_list_wf :
    forall (src_list: list Imp.programL) srcl
      (WFPROGS: Forall wf_prog src_list)
      (LINKED: link_imp_list src_list = Some srcl),
      <<WFLINK: wf_prog srcl>>.
  Proof.
    i. destruct src_list as [| src0 src_list]; ss; clarify.
    depgen src0. depgen srcl. induction src_list; i; ss; clarify.
    { inv WFPROGS. ss. }
    rename a into src1. des_ifs; ss; clarify. rename p into srct.
    hexploit IHsrc_list.
    2:{ eapply Heq. }
    { inv WFPROGS. ss. }
    i. red. eapply linked_two_wf with (src1:=src0) (src2:=srct); eauto.
    inv WFPROGS. auto.
  Qed.

  Lemma linked_list_wf_lift :
    forall (src_list: list Imp.program) srcl
      (LINKED: link_imps src_list = Some srcl),
      <<WFLINK: wf_prog srcl>>.
  Proof.
    i. unfold link_imps in LINKED. assert (WFPROGS: Forall wf_prog (List.map lift src_list)).
    { clear LINKED. clear srcl. induction src_list; ss; clarify. econs; auto. apply lifted_then_wf. }
    hexploit linked_list_wf; eauto.
  Qed.

End PROOF.
