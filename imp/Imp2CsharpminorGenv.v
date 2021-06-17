From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
From ExtLib Require Import Data.List.
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
Require Import AList.

Require Import Imp2CsharpminorMatch.

From compcert Require Import Csharpminor.

Set Implicit Arguments.

Section GENV.

  Context `{Σ: GRA.t}.

  Variable src : Imp.programL.

  Lemma found_imp_function
        f mn fn impf
        (FOUND : find
                   ((fun '(k2, _) => f ?[ eq ] k2) <*>
                    (fun '(mn, (fn, f)) => (fn, transl_all mn ∘ cfun (eval_imp (Sk.sort (defsL src)) f)))) (prog_funsL src) =
                 Some (mn, (fn, impf)))
    :
      (fn = f) /\ (In (mn, (fn, impf)) (prog_funsL src)).
  Proof.
    apply find_some in FOUND. des. split; auto.
    unfold compose in FOUND0. rewrite eq_rel_dec_correct in FOUND0. des_ifs.
  Qed.

  Lemma gm_int_fun_exists
        gm mn fn impf
        (GMAP: get_gmap src = Some gm)
        (INSRC: In (mn, (fn, impf)) (prog_funsL src))
    :
      exists g, In (s2p fn, Gfun (Internal g)) (_int_funs gm).
  Proof.
    unfold get_gmap in GMAP. uo; des_ifs. ss. clear l0.
    unfold pre_compile_iFuns in Heq0. des_ifs.
    rewrite List.map_map in f.
    rewrite Forall_forall in f.
    do 2 (rewrite List.map_map).
    match goal with
    | [ |- exists _, In _ (List.map ?_mapf _) ] =>
      set (mapf:=_mapf) in *
    end.
    assert (SAVED: In (mn, (fn, impf)) (prog_funsL src)); auto.
    apply (in_map mapf _ _) in INSRC.
    subst mapf. ss. des_ifs.
    - exists f0. apply INSRC.
    - specialize f with (x:=None). ss.
      match goal with
      | [ f : In _ (List.map ?_mapf _) -> _ |- _ ] =>
        set (mapf:=_mapf) in *
      end.
      apply (in_map mapf _ _) in SAVED. subst mapf.
      ss. rewrite Heq0 in SAVED. ss.
  Qed.

  Lemma exists_compiled_function
        gm cfs mn fn impf
        (GMAP: get_gmap src = Some gm)
        (COMP: get_iFuns gm (_int_funs gm) = Some cfs)
        (INSRC: In (mn, (fn, impf)) (prog_funsL src))
    :
      exists precf cf,
        (pre_compile_function fn impf = Some precf /\
         In (s2p fn, Gfun (Internal precf)) (_int_funs gm) /\
         get_function gm (s2p fn) (Gfun (Internal precf)) = Some (Gfun (Internal cf)) /\
         In (s2p fn, Gfun (Internal cf)) cfs).
  Proof.
    Local Opaque get_function.
    unfold get_gmap in GMAP. uo; des_ifs. ss.
    match goal with
    | [ COMP: get_iFuns ?_gm _ = Some _ |- _ ] =>
      set (gm:=_gm) in *
    end.
    unfold pre_compile_iFuns in Heq0. des_ifs; ss.
    rewrite List.Forall_map in f. rewrite List.Forall_map in f.
    rewrite Forall_forall in f. hexploit f.
    { apply INSRC. }
    i. ss. des_ifs; ss; clarify. exists f0.
    unfold get_iFuns in COMP. des_ifs; ss.
    do 4 (rewrite List.Forall_map in f1). rewrite Forall_forall in f1.
    hexploit f1.
    { apply INSRC. }
    i. ss. des_ifs; ss; clarify.
    Local Transparent get_function.
    assert (SAVED: get_function gm (s2p fn) (Gfun (Internal f0)) = Some g0); auto.
    unfold get_function in Heq2. uo. destruct (compile_stmt gm (fn_body2 f0)) eqn:CSF0.
    2:{ clarify. }
    match goal with
    | [ Heq2: Some (Gfun (Internal ?_cf)) = Some _ |- _ ] =>
      set (cf:=_cf)
    end.
    clarify.
    Local Opaque get_function.
    exists cf.
    split; auto. split; auto.
    { do 2 (rewrite List.map_map).
      match goal with
      | [ |- In _ (List.map ?_mapf _) ] =>
        set (mapf:=_mapf) in *
      end.
      apply (in_map mapf _ _) in INSRC.
      subst mapf. ss. des_ifs. }

    split; auto.
    do 4 (rewrite List.map_map).
    match goal with
    | [ |- In _ (List.map ?_mapf _) ] =>
      set (mapf:=_mapf) in *
    end.
    apply (in_map mapf _ _) in INSRC.
    assert (mapf (mn, (fn, impf)) = (s2p fn, Gfun (Internal cf))).
    { subst mapf. ss. rewrite Heq1. rewrite SAVED. ss. }
    rewrite <- H1. auto.
    Local Transparent get_function.
  Qed.

  Lemma exists_compiled_variable
        gm gn v
        (GMAP: get_gmap src = Some gm)
        (INSRC: In (gn, v) (prog_varsL src))
    :
      exists cv, In (s2p gn, Gvar cv) (_int_vars gm).
  Proof.
    Local Opaque get_function.
    unfold get_gmap in GMAP. uo; des_ifs. ss. clear Heq0.
    unfold compile_iVars.
    match goal with
    | [ |- exists _, In _ (List.map ?_mapf _) ] => set (mapf:=_mapf) in *
    end.
    apply (in_map mapf _ _) in INSRC. ss. eexists. eapply INSRC.
    Local Transparent get_function.
  Qed.

  Lemma in_tgt_prog_defs_ifuns
        gm tgt mn fn impf precf cf
        (GMAP: get_gmap src = Some gm)
        (COMP: compile src = OK tgt)
        (INSRC: In (mn, (fn, impf)) (prog_funsL src))
        (PRECF: pre_compile_function fn impf = Some precf)
        (COMPF: get_function gm (s2p fn) (Gfun (Internal precf)) = Some (Gfun (Internal cf)))
    :
      In (s2p fn, Gfun (Internal cf)) tgt.(prog_defs).
  Proof.
    unfold compile in COMP. unfold _compile in COMP. des_ifs.
    unfold compile_gdefs in Heq0. uo; des_ifs.
    hexploit exists_compiled_function; eauto. i. des. clarify. ss.
    match goal with
    | [ |- In _ (Maps.PTree.elements (Maps.PTree_Properties.of_list ?_deflist)) ] => set (deflist:=_deflist) in *
    end.
    rename l0 into NOREPET. eapply Maps.PTree_Properties.of_list_norepet in NOREPET.
    { eapply Maps.PTree.elements_correct. eapply NOREPET. }
    subst deflist. do 2 (apply in_or_app; right). ss. do 2 right. apply in_or_app; left. auto.
  Qed.

  Lemma in_tgt_prog_defs_efuns
        gm tgt fn sig
        (GMAP: get_gmap src = Some gm)
        (COMP: compile src = OK tgt)
        (INSRC: In (fn, sig) (ext_funsL src))
    :
      In (s2p fn, Gfun (External (EF_external fn (make_signature sig)))) tgt.(prog_defs).
  Proof.
    unfold compile in COMP. unfold _compile in COMP. des_ifs.
    unfold compile_gdefs in Heq0. uo; des_ifs. ss.
    rename l0 into NOREPET. eapply Maps.PTree_Properties.of_list_norepet in NOREPET.
    { eapply Maps.PTree.elements_correct. eapply NOREPET. }
    apply in_or_app. left. depgen fn. depgen Heq. clear; i.
    unfold get_gmap in Heq. uo; des_ifs; ss; clarify.
    unfold compile_eFuns. rewrite List.map_map.
    match goal with
    | [ |- In _ (List.map ?_mapf _) ] =>
      set (mapf:=_mapf) in *
    end.
    apply (in_map mapf _ _) in INSRC.
    match goal with
    | [ INSRC: In ?p0 _ |- In ?p1 _ ] =>
      replace p1 with p0; auto
    end.
  Qed.

  Lemma compiled_function_props
        gm fn impf precf cf
        (NOMAIN: fn <> "main")
        (GMAP: get_gmap src = Some gm)
        (PRECF: pre_compile_function fn impf = Some precf)
        (COMPF: get_function gm (s2p fn) (Gfun (Internal precf)) = Some (Gfun (Internal cf)))
    :
      (cf.(fn_sig) = precf.(fn_sig2)) /\
      (exists tfbody, compile_stmt gm impf.(Imp.fn_body) = Some tfbody /\
                 cf.(fn_body) = Sseq tfbody (Sreturn (Some (Evar (s2p "return"))))) /\
      (cf.(fn_vars) = [] ) /\
      (Coqlib.list_norepet (fn_params cf)) /\
      (Coqlib.list_disjoint (fn_params cf) (fn_temps cf)).
  Proof.
    unfold pre_compile_function in PRECF. uo; des_ifs.
    - apply rel_dec_correct in Heq. clarify.
    - ss. uo; des_ifs; ss.
      { depgen fn. clear. i. apply rel_dec_correct in Heq0. apply s2p_inj in Heq0. clarify. }
      split; auto. split; auto.
      { exists s; split; auto. }
      split; auto. split; auto.
      { apply Coqlib.list_norepet_append_left in l. auto. }
      apply Coqlib.list_norepet_app in l. des; auto.
  Qed.

  Lemma gm_funs_disjoint
        gm
        (GMAP: get_gmap src = Some gm)
    :
      Coqlib.list_disjoint (List.map fst (_int_funs gm)) (List.map fst (_ext_funs gm)).
  Proof.
    unfold get_gmap in GMAP. uo; des_ifs. ss.
    rewrite map_app in l0. rewrite map_app in l0.
    rewrite app_assoc in l0.
    apply Coqlib.list_norepet_append_left in l0.
    rewrite Coqlib.list_norepet_app in l0. des.
    clear Heq0 l0 l1. clarify.
  Qed.

  Lemma gm_unique
        gm fn f g
        (GMAP: get_gmap src = Some gm)
        (IN1: In (s2p fn, f) (gm.(_int_funs) ++ gm.(_ext_funs) ++ gm.(_int_vars) ++ gm.(_ext_vars)))
        (IN2: In (s2p fn, g) (gm.(_int_funs) ++ gm.(_ext_funs) ++ gm.(_int_vars) ++ gm.(_ext_vars)))
    :
      f = g.
  Proof.
    unfold get_gmap in GMAP. uo; des_ifs. ss.
    match goal with
    | [ IN1: In _ ?_ll |- _ ] =>
      remember _ll as ll
    end.
    clear Heq0 Heqll l. move ll before src. revert_until src. induction ll; i; clarify; ss.
    inv l0. des; clarify; ss.
    - apply (in_map fst _ _) in IN2. ss.
    - apply (in_map fst _ _) in IN1. ss.
    - hexploit IHll; eauto.
  Qed.

  Lemma gm_unique_intfun
        gm fn f g
        (GMAP: get_gmap src = Some gm)
        (IN1: In (s2p fn, f) (_int_funs gm))
        (IN2: In (s2p fn, g) (_int_funs gm))
    :
      f = g.
  Proof.
    hexploit gm_unique.
    { eauto. }
    { eapply in_or_app. left. eapply IN1. }
    { eapply in_or_app. left. eapply IN2. }
    auto.
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
    unfold compile in COMP. des_ifs. rename Heq into GMAP. rename g into gm.
    unfold _compile in COMP. des_ifs. rename Heq into CGDEFS. rename l into cgdefs.
    rename l0 into WFCGDEFS.
    match goal with
    | [ INTGT: In _ (prog_defs ?_tgt) |- _ ] =>
      remember _tgt as tgt
    end.
    hexploit prog_defmap_norepet.
    { unfold prog_defs_names. instantiate (1:=tgt). rewrite Heqtgt. ss. eapply Maps.PTree.elements_keys_norepet. }
    { eapply INTGT. }
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
    unfold compile in COMP. des_ifs. rename Heq into GMAP. rename g into gm.
    unfold _compile in COMP. des_ifs. rename Heq into CGDEFS. rename l into cgdefs.
    rename l0 into WFCGDEFS.
    match goal with
    | [ INTGT: In _ (prog_defs ?_tgt) |- _ ] =>
      remember _tgt as tgt
    end.
    hexploit prog_defmap_norepet.
    { unfold prog_defs_names. instantiate (1:=tgt). rewrite Heqtgt. ss. eapply Maps.PTree.elements_keys_norepet. }
    { eapply INTGT. }
    i. apply Genv.find_def_symbol in H. des. clarify.
  Qed.

End GENV.





Section MAPBLK.

  Import Maps.PTree.

  Context `{Σ: GRA.t}.

  Lemma map_blk_after_init :
    forall src blk
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (ALLOCED : blk >= (src_init_nb src)),
      (<<ALLOCMAP: (map_blk src blk) = Pos.of_succ_nat (2 + (ext_len src) + blk)>>).
  Proof.
    i. unfold map_blk. des. des_ifs.
  Qed.

  Lemma gmap_preserves_length :
    forall src gm
      (GAMP: get_gmap src = Some gm),
      (<<EVL: List.length gm.(_ext_vars) = List.length src.(ext_varsL)>>) /\
      (<<EFL: List.length gm.(_ext_funs) = List.length src.(ext_funsL)>>) /\
      (<<IVL: List.length gm.(_int_vars) = List.length src.(prog_varsL)>>) /\
      (<<IFL: List.length gm.(_int_funs) = List.length src.(prog_funsL)>>).
  Proof.
    unfold get_gmap. i. uo; des_ifs; ss. repeat split.
    - unfold compile_eVars. eapply map_length.
    - unfold compile_eFuns. eapply map_length.
    - unfold compile_iVars. eapply map_length.
    - unfold pre_compile_iFuns in Heq0. des_ifs. do 2 (rewrite List.map_map). eapply map_length.
  Qed.

  Lemma Genv_advance_next_length :
    forall (l : list (ident * globdef fundef ())) p,
      <<LEN: Genv.advance_next l p = Pos.of_nat ((List.length l) + (Pos.to_nat p))>>.
  Proof.
    i. depgen p. induction l; i; ss; clarify.
    - sym; apply Pos2Nat.id.
    - rewrite IHl. rewrite Pos2Nat.inj_succ. rewrite <- plus_n_Sm. ss.
  Qed.

  Lemma NoDup_norepeat :
    forall A (l : list A), <<NOREPET: Coqlib.list_norepet l>> <-> NoDup l.
  Proof.
    split; induction l; i; ss; eauto.
    - econs.
    - inv H. econs; eauto.
    - econs.
    - inv H. econs; eauto. eapply IHl; eauto.
  Qed.

  Lemma perm_elements_PTree_norepeat :
    forall A (l : list (elt * A))
      (NOREPET: Coqlib.list_norepet (List.map fst l)),
      <<LEN: Permutation.Permutation (elements (Maps.PTree_Properties.of_list l)) l>>.
  Proof.
    i. eapply Permutation.NoDup_Permutation.
    - apply NoDup_map_inv with (f:= fst). apply NoDup_norepeat. eapply elements_keys_norepet.
    - apply NoDup_map_inv with (f:= fst). apply NoDup_norepeat. auto.
    - i. assert (NOREPET2: Coqlib.list_norepet (List.map fst (elements (Maps.PTree_Properties.of_list l)))).
      { eapply elements_keys_norepet. }
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

  Lemma length_elements_PTree_norepet :
    forall A (l : list (elt * A))
      (NOREPET: Coqlib.list_norepet (List.map fst l)),
      <<LEN: List.length (elements (Maps.PTree_Properties.of_list l)) = List.length l>>.
  Proof.
    i. eapply Permutation.Permutation_length. eapply perm_elements_PTree_norepeat. auto.
  Qed.

  Lemma get_iFuns_length :
    forall g l1 l2 (GET: get_iFuns g l1 = Some l2), List.length l1 = List.length l2.
  Proof.
    i. unfold get_iFuns in GET. des_ifs. rewrite List.map_map. sym; eapply map_length.
  Qed.

  Lemma wfprog_defsL_length :
    forall src
      (WFPROG: Permutation.Permutation
                 ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                 (List.map fst src.(defsL))),
      <<DEFSL: List.length src.(defsL) = List.length src.(prog_varsL) + List.length src.(prog_funsL)>>.
  Proof.
    i. unfold compose in *. do 2 rewrite <- (map_length fst). rewrite <- (map_length (compose fst snd)).
    rewrite <- app_length. eapply Permutation.Permutation_length. apply Permutation.Permutation_sym. auto.
  Qed.

  Lemma map_blk_init_range :
    forall src tgt id b
      (COMP : Imp2Csharpminor.compile src = OK tgt)
      (WFPROG: Permutation.Permutation
                 ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                 (List.map fst src.(defsL)))
      (TGT: Genv.find_symbol (get_tge tgt) id = Some b),
      <<RANGE: (b < (tgt_init_nb src))%positive>>.
  Proof.
    i. unfold get_tge in *. unfold compile, _compile in COMP. des_ifs. unfold compile_gdefs in Heq0.
    uo; des_ifs; ss. unfold Genv.find_symbol in TGT. apply Genv.genv_symb_range in TGT.
    unfold Genv.globalenv in TGT. ss. rewrite Genv.genv_next_add_globals in TGT. ss.
    unfold tgt_init_nb. unfold ext_len, int_len. hexploit gmap_preserves_length; eauto. i; des.
    rewrite Genv_advance_next_length in TGT. rewrite length_elements_PTree_norepet in TGT; eauto.
    rewrite wfprog_defsL_length; auto. repeat rewrite app_length in TGT. ss. rewrite app_length in TGT.
    eapply get_iFuns_length in Heq0. rewrite <- Heq0 in TGT.
    repeat rewrite map_length in TGT.
    rewrite EVL in TGT; rewrite EFL in TGT; rewrite IVL in TGT; rewrite IFL in TGT.
    depgen TGT. clear. i. unfold NW.
    match goal with
    | [ TGT: Coqlib.Plt _ ?l1 |- (_ < ?l2)%positive ] => replace l2 with l1; eauto
    end.
    lia.
  Qed.

  Lemma compiled_then_exists:
    forall src gm l symb  
      (GMAP: get_gmap src = Some gm)
      (COMP : compile_gdefs gm src = Some l)
      (NOREPET : Coqlib.list_norepet (List.map fst l))
      (WFPROG : In symb (List.map fst (prog_varsL src) ++ List.map (compose fst snd) (prog_funsL src))),
    exists gd : globdef fundef (), In (s2p symb, gd) l.
  Proof.
    i. apply in_app_or in WFPROG. des.
    - apply Coqlib.list_in_map_inv in WFPROG. des. destruct x as [vn v].
      unfold compile_gdefs in COMP. uo; des_ifs; ss.
      hexploit exists_compiled_variable; eauto. i; des. exists (Gvar cv).
      apply in_or_app. right. apply in_or_app. right. ss. do 2 right. apply in_or_app; right.
      clear WFPROG0.
      match goal with
      | [ H : In ?y _ |- (In ?x (List.map ?f _)) ] => set (mapf:=f) in *; replace x with (mapf y)
      end.
      2:{ subst mapf. unfold lift_def. ss. }
      apply in_map. auto.
    - apply Coqlib.list_in_map_inv in WFPROG. des. destruct x as [mn [fn impf]].
      unfold compile_gdefs in COMP. uo; des_ifs; ss.
      hexploit exists_compiled_function; eauto. i; des. exists (Gfun (Internal cf)).
      apply in_or_app. right. apply in_or_app. right. ss. do 2 right. apply in_or_app; left; eauto.
  Qed.

  Lemma in_src_in_tgt :
    forall src gm (l: list (ident * globdef fundef ())) symb
      (GMAP: get_gmap src = Some gm)
      (COMP: compile_gdefs gm src = Some l)
      (NOREPET: Coqlib.list_norepet (List.map fst l))
      (WFPROG : In symb (List.map fst (prog_varsL src) ++ List.map (compose fst snd) (prog_funsL src))),
      <<EXISTSIN: exists gd, In (s2p symb, gd) (elements (Maps.PTree_Properties.of_list l))>>.
  Proof.
    i. unfold get_gmap in GMAP. uo; des_ifs; ss.
    assert (NOREPET2: Coqlib.list_norepet (List.map fst l)); auto.
    apply perm_elements_PTree_norepeat in NOREPET. apply Permutation.Permutation_sym in NOREPET.
    assert (IN1: exists gd, In (s2p symb, gd) l).
    { eapply compiled_then_exists; eauto. unfold get_gmap. uo; des_ifs; ss. }
    des. exists gd. 
    eapply Permutation.Permutation_in; eauto.
  Qed.

  Lemma found_in_src_in_tgt :
    forall src tgt blk symb
      (COMP: compile src = OK tgt)
      (WFPROG: Permutation.Permutation
                 ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                 (List.map fst src.(defsL)))
      (SRC: SkEnv.blk2id (get_sge src) blk = Some symb),
      <<TGTFOUND: exists tb, Genv.find_symbol (get_tge tgt) (s2p symb) = Some tb>>.
  Proof.
    i. unfold compile, _compile in COMP. des_ifs. unfold get_sge, get_tge in *. ss.
    eapply Sk.in_env_in_sk in SRC. des. eapply Sk.sort_incl_rev in SRC.
    apply Permutation.Permutation_sym in WFPROG. apply (in_map fst) in SRC. ss.
    eapply Permutation.Permutation_in in WFPROG; eauto. clear SRC def.
    rename Heq into GMAP. rename Heq0 into COMPGDEFS. rename l0 into NOREPET.
    hexploit in_src_in_tgt; eauto. i. des.
    eapply Genv.find_symbol_exists. ss. eapply H.
  Qed.

  Lemma sksort_same_len :
    forall l, <<LEN: Datatypes.length l = Datatypes.length (Sk.sort l)>>.
  Proof.
    i. pose (Sk.SkSort.Permuted_sort l) as SORTED. apply Permutation.Permutation_length in SORTED. eauto.
  Qed.

  Lemma map_blk_neq :
    forall src b1 b2
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (WFPROG: Permutation.Permutation
                 ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                 (List.map fst src.(defsL)))
      (BLK1: b1 >= (src_init_nb src))
      (BLK2: ~ (b2 >= (src_init_nb src))),
      map_blk src b1 <> map_blk src b2.
  Proof.
    i. unfold map_blk. des_ifs; ii; rename H into CONTRA.
    - clear g n. assert (RANGE: (b < (tgt_init_nb src))%positive).
      { eapply map_blk_init_range; eauto. }
      unfold tgt_init_nb in RANGE. unfold src_init_nb in *. lia.
    - clear g n. unfold get_sge, get_tge in *. hexploit found_in_src_in_tgt; eauto. i; des. unfold get_tge in H; clarify.
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
      (WFPROG: Permutation.Permutation
                 ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                 (List.map fst src.(defsL)) /\ Sk.wf src.(defsL)),
      <<INJ: map_blk src b1 = map_blk src b2 -> b1 = b2>>.
  Proof.
    i. des. destruct (ge_dec b1 (src_init_nb src)) eqn:BRANGE1; destruct (ge_dec b2 (src_init_nb src)) eqn:BRANGE2.
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
    apply Sk.sort_wf in WFPROG0. apply Sk.load_skenv_wf in WFPROG0. des.
    apply WFPROG0 in SBLK1. apply WFPROG0 in SBLK2. rewrite SBLK1 in SBLK2. clarify.
  Qed.
  (* MATCHGE : match_ge src (Sk.sort (defsL src)) (Genv.globalenv tgt) *)
  (* blk : nat *)
  (* gn : string *)
  (* gv : Z *)
  (* SGENV : nth_error (Sk.sort (defsL src)) blk = Some (gn, Sk.Gvar gv) *)
  (* tblk := map_blk src blk : Values.block *)
  (* Genv.find_var_info (Genv.globalenv p) tblk = Some gv -> *)


End MAPBLK.
