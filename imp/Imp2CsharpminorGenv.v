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
    (* (FOUND : find *)
    (*            (((fun fnsem : string * (Any.t -> itree EventsL.Es Any.t) => dec f (fst fnsem)) : _ -> bool) <*> *)
    (*             (fun '(mn0, (fn0, f0)) => (fn0, fun a : Any.t => transl_all mn0 (cfun (eval_imp (Sk.load_skenv (defsL src)) f0) a))))  *)
    (*            (prog_funsL src) = Some (mn, (fn, impf))) *)
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


