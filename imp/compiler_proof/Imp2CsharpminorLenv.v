From compcert Require Import Maps Csharpminor.
From ExtLib Require Import Data.List.
Require Import Coqlib.
Require Import PCM.
Require Import Imp.
Require Import Imp2Csharpminor.
Require Import AList.

Require Import Imp2Csharpminor.
Require Import Imp2CsharpminorMatch.

Set Implicit Arguments.

Section LENV.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Lemma alist_update_le
        src (x: string) id v sv le tle
        (ALIST: alist_find x (alist_add id v le) = Some sv)
        (MLE: match_le src le tle)
    :
      Maps.PTree.get (s2p x) (Maps.PTree.set (s2p id) (map_val src v) tle) = Some (map_val src sv).
  Proof.
    ss. des_ifs.
    - rewrite eq_rel_dec_correct in Heq. des_ifs; ss. apply PTree.gss.
    - apply neg_rel_dec_correct in Heq. 
      rewrite PTree.gso.
      2:{ ii. apply Heq. apply s2p_inj in H. ss. }
      inv MLE. apply ML; eauto.
      rewrite alist_remove_find_neq in ALIST; eauto.
  Qed.

  Lemma bind_parameters_exists_if_smae_length
        params args tle0
        (LEN: List.length params = List.length args)
    :
      exists tle, (<<BIND: bind_parameters params args tle0 = Some tle>>).
  Proof.
    depgen args. depgen tle0. clear. induction params; i; ss; clarify.
    { exists tle0. des_ifs. }
    destruct args; ss; clarify. eauto.
  Qed.

  Lemma bind_parameters_exists
        src base params le rvs (tle0: temp_env)
        (ARGS: init_args params rvs base = Some le)
    :
      exists tle, (<<BIND: bind_parameters (List.map s2p params) (List.map (map_val src) rvs) tle0
                      = Some tle>>).
  Proof.
    eapply bind_parameters_exists_if_smae_length; eauto.
    rewrite ! map_length. eapply init_args_prop; eauto.
  Qed.

  Lemma init_lenv_match
        src le tle l
        (SINIT: le = init_lenv l)
        (TINIT: tle = create_undef_temps (List.map s2p l))
    :
      <<MLINIT: match_le src le tle >>.
  Proof.
    red. depgen src. depgen le. depgen tle. clear. induction l; ii; ss; clarify.
    match goal with
    | [ |- match_le _ (_ :: ?_le0) (PTree.set _ _ ?_tle0)] => specialize IHl with (tle:=_tle0) (le:=_le0) (src:=src) end.
    hexploit IHl; eauto. clear IHl. i. inv H.
    econs. i. ss. des_ifs.
    { rewrite eq_rel_dec_correct in Heq. des_ifs. rewrite PTree.gss. ss. }
    apply neg_rel_dec_correct in Heq.
    rewrite PTree.gso; eauto. ii. apply Heq. apply s2p_inj in H0. ss.
  Qed.

  Lemma _initial_lenv_match
        src params rvs le0 le (tle0: temp_env) tle
        (ML0: match_le src le0 tle0)
        (ARGS: init_args params rvs le0 = Some le)
        (BIND: bind_parameters (List.map s2p params)
                               (List.map (map_val src) rvs) tle0
               = Some tle)
    :
      (<<MLINIT: match_le src le tle>>).
  Proof.
    red. move params before builtins. revert_until params. clear. induction params; i; ss; clarify.
    { destruct rvs; ss; clarify. }
    destruct rvs eqn:RVS; ss; clarify.
    eapply IHparams.
    2: eapply ARGS.
    2: eapply BIND.
    depgen ML0. clear; i. econs; i. eapply alist_update_le; eauto.
  Qed.

  Lemma initial_lenv_match
        src impf rvs le0 le (tle0: temp_env)
        (SINIT: le0 = init_lenv (impf.(Imp.fn_vars) ++ ["return"; "_"]))
        (ARGS: init_args impf.(Imp.fn_params) rvs le0 = Some le)
        (TINIT: tle0 = create_undef_temps
                         (List.map (fun vn : string => s2p vn) (impf.(Imp.fn_vars) ++ ["return"; "_"])))
    :
      exists tle, (<<BIND: bind_parameters
                        (List.map (fun vn : string => s2p vn) impf.(Imp.fn_params))
                        (List.map (map_val src) rvs) tle0 = Some tle>>) /\
             (<<MLINIT: match_le src le tle>>).
  Proof.
    hexploit bind_parameters_exists; eauto. i. des.
    exists tle. split; eauto.
    eapply _initial_lenv_match; eauto.
    eapply init_lenv_match; eauto.
  Qed.

End LENV.
