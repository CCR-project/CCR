From compcert Require Import Maps Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
From ExtLib Require Import Data.List.
Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import AList.

Require Import Imp2Csharpminor.
Require Import Imp2CsharpminorMatch.

From compcert Require Import Csharpminor.

Import Permutation.

Set Implicit Arguments.

Section GENV.

  Context `{Σ: GRA.t}.
  Context `{builtins: builtinsTy}.

  Variable src : Imp.programL.

  Lemma found_imp_function
        f mn fn impf
        (FOUND : find
                   ((fun '(k2, _) => f ?[ eq ] k2) <*>
                     (fun '(mn, (fn, f)) =>
                      (fn, transl_all mn (T:=_) ∘ cfunU (eval_imp (Sk.load_skenv (Sk.sort (defsL src))) f)))) (prog_funsL src) =
                 Some (mn, (fn, impf)))
    :
      (fn = f) /\ (In (mn, (fn, impf)) (prog_funsL src)).
  Proof.
    apply find_some in FOUND. des. split; auto.
    unfold compose in FOUND0. rewrite eq_rel_dec_correct in FOUND0. des_ifs.
  Qed.

  Lemma in_compile_gdefs_ifuns
        ifun
        (INSRC: In ifun (prog_funsL src))
    :
      <<INTGT: In (compile_iFun ifun) (compile_gdefs src)>>.
  Proof.
    red. unfold compile_gdefs. do 4 (apply in_or_app; right). apply in_or_app; left.
    unfold compile_iFuns. apply in_map; auto.
  Qed.

  Lemma in_compile_gdefs_efuns
        efun
        (INSRC: In efun (ext_funsL src))
    :
      <<INTGT: In (compile_eFun efun) (compile_gdefs src)>>.
  Proof.
    red. unfold compile_gdefs. do 2 (apply in_or_app; right). apply in_or_app; left.
    unfold compile_eFuns. apply in_map; auto.
  Qed.

  Lemma in_compile_gdefs_ivars
        ivar
        (INSRC: In ivar (prog_varsL src))
    :
      <<INTGT: In (compile_iVar ivar) (compile_gdefs src)>>.
  Proof.
    red. unfold compile_gdefs. do 5 (apply in_or_app; right).
    unfold compile_iVars. apply in_map; auto.
  Qed.

  Lemma in_compile_gdefs_evars
        evar
        (INSRC: In evar (ext_varsL src))
    :
      <<INTGT: In (compile_eVar evar) (compile_gdefs src)>>.
  Proof.
    red. unfold compile_gdefs. do 3 (apply in_or_app; right). apply in_or_app; left.
    unfold compile_eVars. apply in_map; auto.
  Qed.

  Lemma in_compile_gdefs_init_g
        ig
        (INSRC: In ig init_g)
    :
      <<INTGT: In ig (compile_gdefs src)>>.
  Proof.
    red. unfold compile_gdefs. do 1 (apply in_or_app; left). auto.
  Qed.

  Lemma in_compile_gdefs_c_sys
        sc
        (INSRC: In sc syscalls)
    :
      <<INTGT: In (compile_eFun sc) (compile_gdefs src)>>.
  Proof.
    red. unfold compile_gdefs. do 1 (apply in_or_app; right). apply in_or_app; left.
    unfold c_sys. apply in_map; auto.
  Qed.

  Lemma in_tgt_prog_defs_ifuns
        tgt ifun
        (COMP: compile src = OK tgt)
        (INSRC: In ifun (prog_funsL src))
    :
      <<INTGT: In (compile_iFun ifun) tgt.(prog_defs)>>.
  Proof.
    unfold compile in COMP. des_ifs_safe. red. simpl. apply in_compile_gdefs_ifuns in INSRC.
    set (cf:= compile_iFun ifun) in *. destruct ifun. destruct p. unfold compile_iFun in cf; simpl.
    eapply (PTree_Properties.of_list_norepet _ (fst cf) (snd cf)) in l; eauto.
    eapply PTree.elements_correct. subst cf; ss.
  Qed.

  Lemma in_tgt_prog_defs_efuns
        tgt efun
        (COMP: compile src = OK tgt)
        (INSRC: In efun (ext_funsL src))
    :
      <<INTGT: In (compile_eFun efun) tgt.(prog_defs)>>.
  Proof.
    unfold compile in COMP. des_ifs_safe. red. simpl. apply in_compile_gdefs_efuns in INSRC.
    set (cf:= compile_eFun efun) in *. destruct efun. unfold compile_eFun in cf. simpl.
    eapply (PTree_Properties.of_list_norepet _ (fst cf) (snd cf)) in l; eauto.
    eapply PTree.elements_correct. subst cf; ss.
  Qed.

  Lemma in_tgt_prog_defs_ivars
        tgt ivar
        (COMP: compile src = OK tgt)
        (INSRC: In ivar (prog_varsL src))
    :
      <<INTGT: In (compile_iVar ivar) tgt.(prog_defs)>>.
  Proof.
    unfold compile in COMP. des_ifs_safe. red. ss. apply in_compile_gdefs_ivars in INSRC.
    set (cf:= compile_iVar ivar) in *. destruct ivar. unfold compile_iFun in cf; ss.
    eapply (PTree_Properties.of_list_norepet _ (fst cf) (snd cf)) in l; eauto.
    eapply PTree.elements_correct. subst cf; ss.
  Qed.

  Lemma in_tgt_prog_defs_evars
        tgt evar
        (COMP: compile src = OK tgt)
        (INSRC: In evar (ext_varsL src))
    :
      <<INTGT: In (compile_eVar evar) tgt.(prog_defs)>>.
  Proof.
    unfold compile in COMP. des_ifs_safe. red. ss. apply in_compile_gdefs_evars in INSRC.
    set (cf:= compile_eVar evar) in *. unfold compile_eVar in cf; ss.
    eapply (PTree_Properties.of_list_norepet _ (fst cf) (snd cf)) in l; eauto.
    eapply PTree.elements_correct. subst cf; ss.
  Qed.

  Lemma in_tgt_prog_defs_init_g
        tgt ig
        (COMP: compile src = OK tgt)
        (INSRC: In ig init_g)
    :
      <<INTGT: In ig tgt.(prog_defs)>>.
  Proof.
    unfold compile in COMP. des_ifs_safe. red. ss. apply in_compile_gdefs_init_g in INSRC.
    destruct ig. eapply (PTree_Properties.of_list_norepet _ i g) in l; eauto.
    eapply PTree.elements_correct. ss.
  Qed.

  Lemma in_tgt_prog_defs_c_sys
        tgt sc
        (COMP: compile src = OK tgt)
        (INSRC: In sc syscalls)
    :
      <<INTGT: In (compile_eFun sc) tgt.(prog_defs)>>.
  Proof.
    unfold compile in COMP. des_ifs_safe. red. ss. apply in_compile_gdefs_c_sys in INSRC.
    set (cf:= compile_eFun sc) in *. unfold compile_eFun in cf; ss. destruct sc; ss.
    eapply (PTree_Properties.of_list_norepet _ (fst cf) (snd cf)) in l; eauto.
    eapply PTree.elements_correct. subst cf; ss.
  Qed.

  Lemma tgt_genv_match_symb_def
        tgt name b gd1 gd2
        (COMP: compile src = OK tgt)
        (GFSYM: Genv.find_symbol (Genv.globalenv tgt) (s2p name) = Some b)
        (GFDEF: Genv.find_def (Genv.globalenv tgt) b = Some gd1)
        (INTGT: In (s2p name, gd2) (prog_defs tgt))
    :
      gd1 = gd2.
  Proof.
    unfold compile in COMP. des_ifs_safe. hexploit prog_defmap_norepet; eauto; ss.
    { unfold prog_defs_names. ss. apply PTree.elements_keys_norepet. }
    i. apply Genv.find_def_symbol in H. des. clarify.
  Qed.

  Lemma tgt_genv_find_def_by_blk
        tgt name b gd
        (COMP: compile src = OK tgt)
        (GFSYM: Genv.find_symbol (Genv.globalenv tgt) (s2p name) = Some b)
        (INTGT: In (s2p name, gd) (prog_defs tgt))
    :
      Genv.find_def (Genv.globalenv tgt) b = Some gd.
  Proof.
    unfold compile in COMP. des_ifs_safe. hexploit prog_defmap_norepet; eauto; ss.
    { unfold prog_defs_names. ss. apply PTree.elements_keys_norepet. }
    i. apply Genv.find_def_symbol in H. des. clarify.
  Qed.

End GENV.





Section MAPBLK.

  Import Permutation.

  Context `{Σ: GRA.t}.
  Context `{builtins: builtinsTy}.

  Lemma map_blk_after_init :
    forall src blk
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (ALLOCED : blk >= (src_init_nb src)),
      (<<ALLOCMAP: (map_blk src blk) = Pos.of_succ_nat (tgt_init_len + (ext_len src) + (int_len src - sk_len src) + blk)>>).
  Proof. i. unfold map_blk. des. des_ifs. Qed.

  Lemma Genv_advance_next_length :
    forall (l : list (ident * globdef fundef ())) p,
      <<LEN: Genv.advance_next l p = Pos.of_nat ((List.length l) + (Pos.to_nat p))>>.
  Proof.
    i. depgen p. induction l; i; ss; clarify.
    - sym; apply Pos2Nat.id.
    - rewrite IHl. rewrite Pos2Nat.inj_succ. rewrite <- plus_n_Sm. ss.
  Qed.

  Lemma NoDup_norepeat :
    forall A (l : list A), Coqlib.list_norepet l <-> NoDup l.
  Proof.
    split; induction l; i; ss; eauto.
    - econs.
    - inv H. econs; eauto.
    - econs.
    - inv H. econs; eauto.
  Qed.

  Lemma perm_elements_PTree_norepeat :
    forall A (l : list (PTree.elt * A))
      (NOREPET: Coqlib.list_norepet (List.map fst l)),
      <<LEN: Permutation (PTree.elements (Maps.PTree_Properties.of_list l)) l>>.
  Proof.
    i. eapply NoDup_Permutation.
    - apply NoDup_map_inv with (f:= fst). apply NoDup_norepeat. eapply PTree.elements_keys_norepet.
    - apply NoDup_map_inv with (f:= fst). apply NoDup_norepeat. auto.
    - i. assert (NOREPET2: Coqlib.list_norepet (List.map fst (PTree.elements (Maps.PTree_Properties.of_list l)))).
      { eapply PTree.elements_keys_norepet. }
      destruct x as [ID NODE]. split; i.
      + hexploit Maps.PTree_Properties.of_list_norepet.
        { eapply NOREPET2. }
        { eapply H. }
        i. rewrite Maps.PTree_Properties.of_list_elements in H0. eapply Maps.PTree_Properties.in_of_list in H0. auto.
      + hexploit Maps.PTree_Properties.of_list_norepet.
        { eapply NOREPET. }
        { eapply H. }
        i. eapply Maps.PTree_Properties.in_of_list. rewrite Maps.PTree_Properties.of_list_elements. auto.
  Qed.

  Lemma perm_elements_PTree_norepeat_in_in :
    forall A (l : list (PTree.elt * A))
      (NOREPET: Coqlib.list_norepet (List.map fst l)),
      <<IN: forall x, In x (PTree.elements (Maps.PTree_Properties.of_list l)) <-> In x l>>.
  Proof.
    ii. split; i.
    - eapply Permutation_in.
      2:{ eauto. }
      apply perm_elements_PTree_norepeat. auto.
    - eapply Permutation_in.
      2:{ eauto. }
      apply Permutation_sym. apply perm_elements_PTree_norepeat. auto.
  Qed.

  Lemma length_elements_PTree_norepet :
    forall A (l : list (PTree.elt * A))
      (NOREPET: Coqlib.list_norepet (List.map fst l)),
      <<LEN: List.length (PTree.elements (Maps.PTree_Properties.of_list l)) = List.length l>>.
  Proof.
    i. eapply Permutation_length. eapply perm_elements_PTree_norepeat. auto.
  Qed.

  (* Lemma wfprog_defsL_length : *)
  (*   forall src *)
  (*     (WFPROG: Permutation.Permutation *)
  (*                ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL))) *)
  (*                (List.map fst src.(defsL))), *)
  (*     <<DEFSL: List.length src.(defsL) = List.length src.(prog_varsL) + List.length src.(prog_funsL)>>. *)
  (* Proof. *)
  (*   i. unfold compose in *. do 2 rewrite <- (map_length fst). rewrite <- (map_length (compose fst snd)). *)
  (*   rewrite <- app_length. eapply Permutation.Permutation_length. apply Permutation.Permutation_sym. auto. *)
  (* Qed. *)

  Lemma gdefs_preserves_length :
        forall src,
          <<LEN: List.length (compile_gdefs src) =
                 tgt_init_len + (List.length (ext_varsL src) + List.length (ext_funsL src)) +
                 (List.length (prog_varsL src) + List.length (prog_funsL src)) >>.
  Proof.
    i. red. unfold compile_gdefs. ss. repeat (rewrite app_length).
    unfold tgt_init_len. ss. repeat (rewrite app_length).
    unfold compile_eFuns, compile_eVars, compile_iFuns, compile_iVars. rewrite! map_length. lia.
  Qed.

  Lemma map_blk_init_range :
    forall src tgt id b
      (COMP : Imp2Csharpminor.compile src = OK tgt)
      (TGT: Genv.find_symbol (get_tge tgt) id = Some b),
      <<RANGE: (b < (tgt_init_nb src))%positive>>.
  Proof.
    i. unfold get_tge in *. unfold compile in COMP. des_ifs.
    unfold Genv.find_symbol in TGT. apply Genv.genv_symb_range in TGT.
    unfold Genv.globalenv in TGT. ss. rewrite Genv.genv_next_add_globals in TGT. ss.
    unfold tgt_init_nb. unfold ext_len, int_len.
    rewrite Genv_advance_next_length in TGT. rewrite length_elements_PTree_norepet in TGT; eauto.
    red. rewrite gdefs_preserves_length in TGT.
    match goal with
    | [ TGT: Coqlib.Plt _ ?l1 |- (_ < ?l2)%positive ] => replace l2 with l1; eauto
    end.
    lia.
  Qed.

  Lemma in_src_in_tgt :
    forall src (l: list (ident * globdef fundef ())) symb
      (COMP: compile_gdefs src = l)
      (NOREPET: Coqlib.list_norepet (List.map fst l))
      (WFPROG : In symb (List.map fst (prog_varsL src) ++ List.map (fst ∘ snd) (prog_funsL src) ++
                         (ext_varsL src) ++ List.map fst (ext_funsL src))),
      <<EXISTSIN: exists gd, In (s2p symb, gd) (PTree.elements (Maps.PTree_Properties.of_list l))>>.
  Proof.
    i. assert (NOREPET2: Coqlib.list_norepet (List.map fst l)); auto.
    apply perm_elements_PTree_norepeat in NOREPET. apply Permutation.Permutation_sym in NOREPET.
    apply in_app_or in WFPROG. des.
    { apply Coqlib.list_in_map_inv in WFPROG. des. apply in_compile_gdefs_ivars in WFPROG0.
      clarify. set (ivar:= compile_iVar x) in *. exists (snd ivar).
      eapply Permutation_in; eauto. subst ivar. destruct x; ss. }
    apply in_app_or in WFPROG. des.
    { apply Coqlib.list_in_map_inv in WFPROG. des. apply in_compile_gdefs_ifuns in WFPROG0.
      clarify. set (ifun:= compile_iFun x) in *. exists (snd ifun).
      eapply Permutation_in; eauto. subst ifun. destruct x. destruct p. ss. }
    apply in_app_or in WFPROG. des.
    { apply in_compile_gdefs_evars in WFPROG.
      clarify. set (evar:= compile_eVar symb) in *. exists (snd evar). eapply Permutation_in; eauto. }
    { apply Coqlib.list_in_map_inv in WFPROG. des. apply in_compile_gdefs_efuns in WFPROG0.
      clarify. set (efun:= compile_eFun x) in *. exists (snd efun).
      eapply Permutation_in; eauto. subst efun. destruct x. ss. }
  Qed.

  Lemma found_in_src_in_tgt :
    forall src tgt blk symb
      (COMP: compile src = OK tgt)
      (WFPROG: incl (name1 src.(defsL)) ((name1 src.(prog_varsL)) ++ (name2 src.(prog_funsL))))
      (SRC: SkEnv.blk2id (get_sge src) blk = Some symb),
      <<TGTFOUND: exists tb, Genv.find_symbol (get_tge tgt) (s2p symb) = Some tb>>.
  Proof.
    i. unfold compile in COMP. des_ifs_safe. unfold get_sge, get_tge in *. ss.
    eapply Sk.in_env_in_sk in SRC. des. eapply Sk.sort_incl_rev in SRC.
    apply (in_map fst) in SRC. ss.
    unfold name1, name2 in WFPROG. apply WFPROG in SRC.
    hexploit in_src_in_tgt; eauto.
    { instantiate (1:=symb). rewrite app_assoc. apply in_or_app. left. auto. }
    i. des. eapply Genv.find_symbol_exists. ss. eapply H.
  Qed.

  Lemma sksort_same_len :
    forall l, <<LEN: Datatypes.length l = Datatypes.length (Sk.sort l)>>.
  Proof.
    i. pose (Sk.SkSort.Permuted_sort l) as SORTED. apply Permutation.Permutation_length in SORTED. eauto.
  Qed.

  Lemma wfprog_defsL_length :
    forall src
      (WFPROG: (NoDup (name1 src.(defsL))) /\
               (incl (name1 src.(defsL)) ((name1 src.(prog_varsL)) ++ (name2 src.(prog_funsL))))),
      <<DEFSL: sk_len src <= int_len src>>.
  Proof.
    i. unfold sk_len, int_len. unfold name1, name2 in *.
    do 2 rewrite <- (map_length fst). rewrite <- (map_length (fst ∘ snd)).
    rewrite <- app_length. des. eapply NoDup_incl_length; eauto.
  Qed.

  Lemma map_blk_neq :
    forall src b1 b2
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (WFPROG: (NoDup (name1 src.(defsL))) /\
               (incl (name1 src.(defsL)) ((name1 src.(prog_varsL)) ++ (name2 src.(prog_funsL)))))
      (BLK1: b1 >= (src_init_nb src))
      (BLK2: ~ (b2 >= (src_init_nb src))),
      map_blk src b1 <> map_blk src b2.
  Proof.
    i. unfold map_blk. des_ifs; ii; rename H into CONTRA.
    - clear g n.
      assert (RANGE: (b < (tgt_init_nb src))%positive).
      { eapply map_blk_init_range; eauto. }
      unfold tgt_init_nb in RANGE. unfold src_init_nb in *.
      hexploit (wfprog_defsL_length _ WFPROG). i. des. lia.
    - clear g n. unfold get_sge, get_tge in *. des.
      hexploit found_in_src_in_tgt; eauto. i; des. unfold get_tge in H; clarify.
    - clear g n. unfold get_sge in Heq0. apply not_ge in BLK2. rename Heq0 into NOTFOUND. simpl in NOTFOUND.
      unfold src_init_nb in BLK2. unfold int_len in BLK2.
      assert (SORTED: b2 < Datatypes.length (Sk.sort (defsL src))).
      { rewrite <- sksort_same_len. ss. }
      eapply Sk.env_range_some in SORTED. des. setoid_rewrite SORTED in NOTFOUND. clarify.
    - des. clarify.
  Qed.

  Lemma map_blk_inj :
    forall src b1 b2
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (WFPROG: incl (name1 src.(defsL)) ((name1 src.(prog_varsL)) ++ (name2 src.(prog_funsL))))
      (WFSK: Sk.wf src.(defsL)),
      <<INJ: map_blk src b1 = map_blk src b2 -> b1 = b2>>.
  Proof.
    i.
    assert (NODUP: NoDup (name1 src.(defsL))).
    { unfold Sk.wf in WFSK. ss. }
    des. destruct (ge_dec b1 (src_init_nb src)) eqn:BRANGE1; destruct (ge_dec b2 (src_init_nb src)) eqn:BRANGE2.
    { unfold map_blk. des_ifs. ii. lia. }
    { hexploit map_blk_neq; eauto; ii; clarify. }
    { hexploit map_blk_neq; eauto; ii. sym in H0. clarify. }
    unfold map_blk. unfold src_init_nb in *. unfold int_len in *. unfold get_sge in *.
    rewrite BRANGE1. rewrite BRANGE2. clear BRANGE1 BRANGE2.
    rename n into BLK1. apply not_ge in BLK1. rename n0 into BLK2. apply not_ge in BLK2.
    assert (SBLK1: b1 < Datatypes.length (Sk.sort (defsL src))).
    { rewrite <- sksort_same_len; ss. }
    assert (SBLK2: b2 < Datatypes.length (Sk.sort (defsL src))).
    { rewrite <- sksort_same_len; ss. }
    eapply Sk.env_range_some in SBLK1. eapply Sk.env_range_some in SBLK2. des.
    ss. rewrite SBLK1. rewrite SBLK2. rewrite COMP. ii.
    hexploit found_in_src_in_tgt.
    1,2: eauto.
    { unfold get_sge. ss. eapply SBLK1. }
    hexploit found_in_src_in_tgt.
    1,2: eauto.
    { unfold get_sge. ss. eapply SBLK2. }
    i. des. rewrite H0 in H. rewrite H1 in H. clarify.
    apply Genv.find_invert_symbol in H0. apply Genv.find_invert_symbol in H1.
    rewrite H1 in H0. clear H1. clarify. apply s2p_inj in H0. clarify.
    apply Sk.sort_wf in WFSK. apply Sk.load_skenv_wf in WFSK. des.
    apply WFSK in SBLK1. apply WFSK in SBLK2. rewrite SBLK1 in SBLK2. clarify.
  Qed.

  Lemma found_gvar_in_src_then_tgt :
    forall src tgt blk gn gv
      (COMP : Imp2Csharpminor.compile src = OK tgt)
      (WFSK : Sk.wf src.(defsL))
      (WFPROG2 : forall gn gv, In (gn, Sk.Gvar gv) (Sk.sort (defsL src)) -> In (gn, gv) (prog_varsL src))
      (MATCHGE : match_ge src (Sk.load_skenv (Sk.sort (defsL src))) (Genv.globalenv tgt))
      (SGENV : nth_error (Sk.sort (defsL src)) blk = Some (gn, Sk.Gvar gv)),
      <<FOUNDTGT: exists tgv, (Genv.find_def (Genv.globalenv tgt) (map_blk src blk) = Some (Gvar tgv))>>.
  Proof.
    i. apply Sk.sort_wf in WFSK. set (sge:= Sk.sort (defsL src)) in *. set (tge:= Genv.globalenv tgt) in *.
    assert (SFOUND: SkEnv.blk2id (Sk.load_skenv sge) blk = Some gn).
    { Local Transparent Sk.load_skenv. unfold Sk.load_skenv. ss. rewrite SGENV. uo; ss. Local Opaque Sk.load_skenv. }
    apply Sk.load_skenv_wf in WFSK. apply WFSK in SFOUND. apply nth_error_In in SGENV.
    assert (INTDEFS: exists cv, In (s2p gn, Gvar cv) (prog_defs tgt)).
    { apply WFPROG2 in SGENV. hexploit in_tgt_prog_defs_ivars; eauto. }
    des. hexploit tgt_genv_find_def_by_blk; eauto.
    inv MATCHGE. eapply MG. clear MG. eauto.
  Qed.

  Lemma compiled_gvar_props :
    forall src tgt gn gv tblk tgv
      (COMP : compile src = OK tgt)
      (INSRC : In (gn, gv) (prog_varsL src))
      (FOUNDSYM : Genv.find_symbol (Genv.globalenv tgt) (s2p gn) = Some (tblk))
      (FOUNDTGV : Genv.find_def (Genv.globalenv tgt) (tblk) = Some (Gvar tgv)),
      <<GVARP: (gvar_info tgv = ()) /\ (gvar_init tgv = [Init_int64 (Int64.repr gv)]) /\
               (gvar_readonly tgv = false) /\ (gvar_volatile tgv = false)>>.
  Proof.
    i. hexploit in_tgt_prog_defs_ivars; eauto. i.
    hexploit Genv.find_def_inversion; eauto. i. des.
    hexploit tgt_genv_match_symb_def; eauto. i. clarify.
  Qed.

End MAPBLK.
